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

> **Superseded for the recursion / speculative-search class (S104, §2.8).** This purely
> *syntactic* "non-cheap `Apply`" filter falsifiably over-sparks on divide-and-conquer
> recursion and speculative search (F1 `fib`, F4 Sudoku): it emitted 9.45M tiny sparks on
> F4-hard, cores parked not computing (FIXME 0534). For that class, **§2.8's utilization
> model** replaces this filter — M-static (non-tail recursion) governs *which* candidates
> spark and M-dynamic (busy-core bail-out) governs *how many*. This §2.2 filter stays the
> admission rule for the compute-bound `let`/apply spark classes it still serves.

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

### 2.7 The static allocation/RC-density admission axis (FIXME 0459 gate half — designed S102; implementation rides increment I)

> **DEMOTED + default-flipped OFF at S104 (arch ruling, `effect-concurrency.md` §3.1.1;
> FIXME 0534).** This axis (call it **B4**, its ownership-codegen ladder name) is a
> *contention* proxy built against the S94/S99 (a)/(b) alloc/RC model. 0534 profiled F4-hard
> and proved that for the **recursion / speculative-search workload class** the dominant cost
> is **rayon scheduler churn, not contention**, and that B4 is there **net-harmful, not merely
> neutral**: it declines the coarse divide-and-conquer sparks (they score dense 2/4) while the
> fine score-0 accessor sparks stay admitted, so the fine sparks **strand** on a serialized
> outer tree — 112s (B4 default-on) vs 24s (B4 off, admit-all) vs 0.9s (serial). The
> decline-coarse-while-admitting-nested-fine state is *incoherent*. **This sprint flips
> `SPARK_DENSITY_MAX_DEFAULT` `1 → 0`** (B4 off by default; see §2.8 "B4 default-flip"). The
> *concept* below is **not retired** — it stays valid for the genuinely alloc/RC-dense
> *compute-bound* class (the S99 F2 vec-COW workloads) and may return **Phase-H-composed**
> (scoring the surviving population the memory mechanisms define, per §2.7 "Sequencing"). But
> it is **not** the S104 admission mechanism, it must never default-fire in the incoherent
> state 0534 exposed, and for the recursion/search class **§2.8 supersedes this section's
> framing** (M-static handles *selection* structurally; the as-built worker-origin `SPARK_DEPTH`
> bound — not the concurrent cap — handles *quantity*, §2.8.4). The design text below is preserved
> as-is for the compute-bound class it still serves.
>
> **S105 forward-pointer (as-built):** when the density signal returns it comes back as the
> *depth-gate input* to §2.8.4's `MAX_DEPTH` — a **density-aware depth allowance** (deep for
> alloc-free strands, shallow for alloc-heavy) — **NOT** the admission-*decline* form this section
> designs. See §2.8.8 (the S105 focus) and FIXME 0535.

The contention-aware gate 0459 asked for, static layer (`effect-concurrency.md` §3.1's
first layer). The dynamic layer landed opt-in as the saturation gate (§3.6.3) and stays
deferred with the FIXME-0442 unified-budget family; this section designs the **static
axis** — the piece that becomes possible only now, because the ownership-inference read
path (`design/backend/ownership-codegen.md`; spine `design/arch/ownership-inference.md`
§8.3) supplies the signal the S94 create-gate could not see: *which of a branch's
allocations and RC ops actually survive*.

**The signal — zero new analysis (Principle 7).** Per spark candidate (a `let` binding's
RHS or a sparkable apply argument — the same `MonoExpr` subtree `find_sparkable_bindings`
/ `find_sparkable_args` already walk), a **density score** computed from the per-site
facts `pass5_ownership` annotates:

- +1 per heap-allocation site NOT covered by a `NoEscape` fact (i.e. not
  stack/region-servable — it will contend on the shared allocator);
- +1 per RC-op-emitting site on a cell that is neither `Confined` (it will emit atomic)
  nor borrow-elided (the op survives at all).

Fact-absent sites count as dense (they compile conservative — atomic + heap — which is
precisely the contention being scored). The score is a static per-instantiation proxy for
the S99 (b) term: the concurrent atomic-RC + allocator traffic each of the `cap` live
branches generates.

**The rule.** `is_worth_sparking` (§2.2) gains the density axis alongside the compute
axis: a candidate whose score exceeds the threshold is **declined** — it compiles on the
sequential arm exactly as a cheap candidate does today. Declining is always sound:
granted-vs-direct is a scheduling choice only (§8 observational equivalence), and the
decline direction restores the floor rather than risking it.

**Activation gating — admission-identical when facts are absent (the byte-identity
discipline, ownership-codegen §2.2 applied to a scheduling emission).** The axis is keyed
off "pass5 ran" (the compile unit carries summaries/facts). `CRANELISP_NO_OWNERSHIP=1`,
pre-increment-I builds, and any facts-absent unit ⇒ the axis is **inert** and the
admission set is byte-for-byte today's. (This polarity matters: if the axis naively
scored a facts-absent build, everything would score dense and sparking would vanish —
the wrong failure mode for the oracle toggle.)

**Threshold + knob.** A named constant `SPARK_DENSITY_MAX_DEFAULT` with an env override
(`CRANELISP_SPARK_DENSITY_MAX=N`; `0` disables the axis). **S104: the default is
`0` (disabled)** — flipped from the increment-I `1` per the demotion banner above and
`effect-concurrency.md` §3.1.1. When the axis is re-enabled Phase-H-composed for the
alloc/RC-dense compute-bound class, its non-zero threshold is set **by measurement at that
landing change-set** against the F2/F4 fixtures (must decline their allocation-dominated
shared-data branches) and the fib/compute-bound shapes (must stay admitted — the §9
near-linear-speedup acceptance is unchanged). No non-zero number is pinned in this doc; the
sprint plan's gate is the arbiter. Opt-in `CRANELISP_SPARK_DENSITY_MAX=N` remains available
this sprint as the B4-on diagnostic row of the Stage-0 config matrix.

**Acceptance shape (for `/qa`):** the §9 three-regime equivalence gains a fourth regime
(density-declined ≡ serial ≡ the other three); the F4-hard distribution's parallel wall
must move toward serial when the axis activates; the existing `let`-path perf tests must
be re-checked exactly as §3.6.3's `let`-path note prescribes for the create-gate. Unit
tier: the §2.2 sparkability fixtures extended with the {facts present/absent} ×
{alloc-dense/compute-dense/mixed} × {threshold boundary} matrix
(ownership-codegen §13.5).

**Sequencing.** Implementation = ladder entry **B4** in ownership-codegen §13.2 — after
the borrow-elision / non-atomic / stack-slot mechanisms, because the score measures the
*surviving* population those mechanisms define. The Phase-H structural cure (the
mechanisms themselves) remains the primary attack on the S99 term; this axis is the
scheduler-side complement that stops sparking the branches the mechanisms cannot yet
serve.

### 2.8 The utilization model — spark for core occupancy, not fine-grained parallelism (Sprint 104)

> **AS-BUILT (S104 Waves 1–2e; reconciled Phase 5).** This section was authored pre-implementation
> (Phase 3). Measurement moved two rulings; the mechanism text below is reconciled to what shipped.
> **(1)** M-static (§2.8.2) shipped as-designed — `admit? = (in recursive SCC) ∧ ¬in_tail_position`,
> toggle `CRANELISP_SPARK_ADMIT=mstatic|syntactic`, default `mstatic`. **(2)** The M-dynamic
> *concurrent cap* does **NOT** bound cumulative spawn count — permits recycle on completion, so F5
> stayed ~1.5M spawns at *every* cap (§2.8.3). Structural hierarchical decline is therefore
> **MANDATORY, not optional**, and shipped as a **worker-origin thread-local `SPARK_DEPTH`** with
> cross-spawn base propagation, default `MAX_DEPTH = floor(log2(nproc)) = 3` (§2.8.4). A both-paths
> variant was measured harmful (collapsed to peak 2); pure worker-only with no allowance made F3 7.5×
> slower — the depth-allowed worker-origin form fills the cores. **(3)** `ivar_force` now backs off
> (`spin → yield_now → sleep`), CPU hygiene not a wall fix (§2.8.4 backoff block). The §2.8.7
> measurement doctrine and §2.8.8 remaining-problems/limits (S105 density-aware depth, budget-inline
> ceiling, alloc/RC floor, F4-at-D3 trade) are the honest open record. Cross-ref
> `effect-concurrency.md` §3.1.1–3.1.5 (arch, updated in parallel).

**Measured outcome (S104 Waves 1–2e; D=3 default) — the headline result.** Compute-parallel wins and
the pathology cure (see §2.8.8 for the limits and open work these numbers sit against; not duplicated
here):

| Fixture | Serial | Parallel (as-built) | Result |
|---|---|---|---|
| F6 — 16 heavy balanced (alloc-free) leaves | 3.10s | 0.82s | **3.4× speedup** |
| F5 — `fib` recursive fork | 0.67s | 0.39s | **1.7× speedup** |
| F4-hard — Sudoku speculative search | ~55s | ~2.3s | **pathology cured** (spawns collapsed ~6 orders of magnitude) |

**The limit (deliberately out of scope this sprint — the set-aside memory class):** alloc/RC-contended
search (F3, and the alloc-heavy part of F4) stays *above* serial. The uniform depth allowance cannot
distinguish alloc-free compute fan-out (F6, wins) from alloc-heavy *contended* fan-out (F4, loses) —
the distinguishing signal is **allocation/RC density**, the deliberately-set-aside memory work. That is
the **S105 focus (§2.8.8): a density-aware depth allowance** — deep for alloc-free strands, shallow for
alloc-heavy — composed with the Phase-H memory cure. The **budget-inline depth-leak ceiling** (`D`
cannot exceed ~`log2(cap)`; F5 re-explodes to 1.3M spawns at D=4 without a backend hook on the
create-gate inline arm) is recorded in §2.8.8; the shipped D=3 sits safely under it.

This section supersedes the §2.2 syntactic filter and the §2.7 density-axis framing **for the
recursion / speculative-search workload class** (F1 `fib`/`reduce-tree`, F4 Sudoku
`solve-range`). Its thesis home is `effect-concurrency.md` §3.1.1–3.1.4 (arch-ruled, S104
Phase 2); this section is the backend **mechanism** design. The §2.2/§2.5/§2.6 filters and the
§2.7 concept stay valid for the classes they still serve (compute-bound `let`/apply sparks, the
alloc/RC-dense compute class); §2.8 replaces *how a candidate is admitted* for the class where
the syntactic filter falsifiably over-sparks.

**The reframe (why the old model failed — the actors tell the story below).** The §2.2 filter
is purely *syntactic*: "a non-cheap `Apply`" is worth sparking. On F4-hard that emits **9.45M
tiny sparks clustered at the work frontier** — the 104 score-0 `(cell-at g i)` accessor pairs
in per-cell hot loops — each paying a ~13µs spawn/wake/park round-trip against a ~20ns body
(0534: `wall ≈ serial + spawns × per-spark-overhead`; ~600× overhead-to-work ratio; 240% CPU on
10 cores = cores *parked in futex*, not computing). The goal is **not** fine-grained
parallelism. The goal is **core utilization**: dispatch a *small* number — on the order of
**~2 per core** — of distinct, probably-large work items that **separate** onto different cores
and then each run forward on an **efficient sequential path**. Populate the cores, then get out
of the way. The old model had a *create-gate* (§3.6, bounds concurrent IVar count → memory) but
no *utilization gate*: it estimated neither the benefit (is this piece big enough to be worth
separating?) nor the cost (are the cores already busy?) of a spark.

#### 2.8.1 Actors and the functions between them (before any mechanism — Principle 21)

The mechanism is meaningless until the actors and the functions between them are explicit. Four
actors participate in every spark:

| Actor | What it is | Where it lives |
|---|---|---|
| **Producer** | the codegen decision site that, per candidate work item (a `let` binding RHS or an apply argument), chooses *spark* (emit the IVar/thunk on the lenient arm) or *inline* (the direct arm). | `compile_let` §4.1 / `compile_apply` §4.4 — compile-time for quality, emits a runtime branch for quantity |
| **Pool / cores** | the fixed rayon work-stealing pool of `ncores` worker threads — the **shared resource being utilized**. | `ivar_spark` → `rayon::spawn` (§3.4) |
| **Strand** | a dispatched spark body — one IVar's thunk running its **sequential subtree** forward on a worker. "Good" work is a strand that separated onto its own core and runs straight-line. | the spawned closure in `ivar_spark` |
| **Consumer / forcer** | the code that joins a strand back — forces the IVar at the barrier before the enclosing call/body. | `ivar_force` at the §4.2/§4.4 Phase-2 barrier |

The **functions** between them (each with its cost, which is the whole point):

1. **produce-or-inline** (Producer → {spark, inline}). The admission decision. Cost: compile-time
   (the *quality* axis, M-static) plus **one atomic** at runtime (the *quantity* axis, M-dynamic's
   create-gate `try_reserve`). This is the function the utilization model redesigns.
2. **dispatch** (Producer → Pool). `ivar_create` + `ivar_spark` + `rayon::spawn`. Cost ≈ **13µs**
   of wake/park/steal round-trip (0534). Only worth paying if the strand then **separates** onto an
   idle core and runs a body far larger than 13µs.
3. **sequential execution** (Strand on a core). The strand runs its subtree straight-line, **with no
   further sparking inside it**. This is where the useful work happens; it must dominate the
   dispatch cost.
4. **force / join** (Consumer ← Strand). `ivar_force` (§3.5): RESOLVED fast-path, spin-wait, or
   claim-compute (work conservation). If the consumer forces *almost immediately* after dispatch (a
   near-immediate data dependency, exactly F4's accessor pairs), the strand never got to run forward
   — the dispatch cost bought nothing.

**What "good" looks like.** ~2/core distinct **large** strands that (i) **separate** — each spawned
onto a distinct otherwise-idle core, not clustered at the frontier — and (ii) then **run a
high-efficiency sequential path** — no nested spawns, no per-node dispatch cost. Cores **busy**
(F4 admit-all coarse: 565% CPU on 10 cores, workers computing) rather than **parked** (F4
default: 240%, workers in `futex_do_wait`). Small count, large bodies — the exact inverse of 9.45M
tiny sparks.

**The two failure modes the model must structurally avoid**, named against the actors:

- **Over-production at the frontier** — the Producer emits millions of tiny candidates (function 1
  fires indiscriminately); dispatch (function 2) dominates; strands never separate (all at the
  frontier); the Consumer forces immediately (function 4), so sequential execution (function 3)
  never happens. *This is the F4 firehose.* → cured by **M-static** (stop producing the fine
  candidates). *(As-built note: the concurrent cap does NOT then bound the residual count — §2.8.3;
  the depth explosion is cured separately below.)*
- **Internal re-explosion** — the Producer emits coarse strands, but each strand *re-produces*
  internally (a divide-and-conquer recursion is non-tail-recursive at every level, so the same
  quality signal re-fires all the way down); the tree explodes again from within. → cured by
  **worker-origin depth decline** (§2.8.4, as-built MANDATORY): a dispatched strand stops sparking
  once its logical nesting depth reaches `MAX_DEPTH`.

#### 2.8.2 M-static — the quality axis (spark coarse, not fine)

**Rule.** For this class, replace the §2.2 syntactic "non-cheap `Apply`" filter with a structural
*probably-large* signal: **non-tail recursion** — a candidate `Apply` is sparkable iff

> its resolved callee is a member of a **recursive strongly-connected component (SCC)** of the
> static call graph, **AND** the apply is **not** `in_tail_position`.

**How recursive-SCC membership is derived at codegen — no new interface.** The signal is computed
backend-internally from data that already exists:

- Each persisted `ModuleEntry::Def` carries `callees` (Decision 21) — the set of statically-resolved
  user-fn references the def makes, **FIXME-0470-enriched** to *every* statically-resolved user-fn
  reference (the same edges the ownership fixpoint walks), not just direct top-level calls.
- The backend builds the directed call graph over the loaded defs (nodes = FQ callables, edges =
  `callees`), runs an SCC pass (Tarjan/Kosaraju — plain graph analysis), and marks a callee **in a
  recursive SCC** iff its SCC has >1 node (mutual recursion) **or** it has a self-edge (direct
  self-recursion — a singleton SCC with a self-loop). The result is cached once per compile unit
  and read at each candidate site.
- `in_tail_position` is **already** tracked in the backend (TCO + the §2.5.3 apply-arg gating), so
  the second conjunct is a free read.

Per `effect-concurrency.md` §3.1.2: this uses an **existing** `cranelisp-types` field via
backend-internal analysis — **no new cross-crate type, no schema/baseline cascade, no ABI change**.
Whether "in a recursive SCC" is computed on-demand in backend or materialized as a per-callable
flag is a `/design`/`/dev` interior choice, **provided it stays off the public edge** (it does).
**Soundness is toward decline:** a callee whose `Def` is not yet loaded (incremental dev session),
or reached through a HOF/closure/extern indirection (unresolved), is treated as **non-recursive ⇒
not sparked ⇒ safe** — the same conservative default the launch-eligibility predicate uses
(`effect-concurrency.md` §4.1). Declining is always sound: spark-vs-inline is a scheduling choice
only (§8 observational equivalence).

**Discrimination check (the Stage-0 experiment this must pass).** The signal must separate
beneficial from harmful *structurally*, not by an F4-specific threshold:

| Candidate | Recursive SCC? | Tail? | M-static |
|---|---|---|---|
| F1 `(add-i64 (fib a) (fib b))` | yes (self-edge) | non-tail | **spark** ✓ |
| F1 `reduce-tree` recursive fork | yes | non-tail | **spark** ✓ |
| F4 coarse `(solve-range …)` D&C search | yes | non-tail | **spark** ✓ |
| F4 fine `(cell-at g i)` accessor pair | **no** (flat accessor, no recursive SCC) | non-tail | **decline** ✓ |
| tail-recursive loop step (accumulator) | yes | **tail** | decline (TCO jump; also §2.5.3) |
| flat call in tail position | no | tail | decline |

The 104 F4 score-0 accessor sparks — 0534's pure-overhead firehose — are declined **structurally**
because `cell-at` is in no recursive SCC, while F1's beneficial `fib`/`reduce-tree` sparks and F4's
coarse `solve-range` sparks are kept. This is the quality separation the syntactic filter could not
make (both scored as "non-cheap `Apply`").

**As-built (shipped as-designed) + toggle + measured.** M-static shipped exactly as specified:
`admit? = (in recursive SCC) ∧ ¬in_tail_position`, selectable via
`CRANELISP_SPARK_ADMIT=mstatic|syntactic` (**default `mstatic`**; `syntactic` restores the §2.2
non-cheap-`Apply` filter for A/B measurement). **Measured (F4-hard):** declining the fine
`(cell-at g i)` accessor firehose *structurally* took fine-accessor spawns **13.1M → 182** and wall
**~55s → ~2.4s** — M-static alone is the dominant F4-hard win, because that fine frontier
cross-section was the bulk of the firehose.

**M-static is a QUALITY axis ONLY — it does NOT deliver the ~2/core collapse.** A divide-and-conquer
recursion is non-tail-recursive at *every* level: each `fib`/`solve-range` node re-applies the
recursive callee non-tail, so M-static **re-selects spark sites all the way down the tree** — the
`fib`-explosion shape. M-static prunes the fine *frontier cross-section* (the accessor firehose); it
leaves the recursive *depth* explosion fully intact. **As-built, the count collapse is the
worker-origin `SPARK_DEPTH` mechanism's (§2.8.4), NOT the concurrent cap's** — measurement showed the
cap does not bound cumulative spawns (§2.8.3). Grade F4 as an **M-static × depth-decline interaction**,
not a sum: neither alone clears it (M-static keeps the good work but still explodes in depth; the depth
bound collapses the count but, without M-static, spends its frontier on the fine accessors).

#### 2.8.3 M-dynamic — the measured reversal: the concurrent cap does NOT bound cumulative spawns

**Pre-implementation (Phase 3) this section claimed** the ~2/core collapse was *emergent* from
re-parameterizing the existing create-gate (§3.6.2): tune the `SPARK_BUDGET` cap toward `~2 × ncores`,
flip it default-on, and every deeper recursion site would see a full pool, `try_reserve` returns `0`,
and inline. The create-gate emits, per site:

```
granted = call cranelisp_spark_budget_try_reserve(n)   // 1 = spark (lenient arm), 0 = inline (direct arm)
brif granted, lenient_block, direct_block
```

with `spark_budget_try_reserve` (§3.6.1) returning `1` when `IN_FLIGHT_SPARKS + n ≤ cap`.

**S104 Wave-2 measurement falsified the emergent-collapse claim.** The create-gate counts *concurrent*
in-flight sparks and **recycles permits on completion** — each strand's `InFlightGuard` drop releases a
permit (§3.6.1). A divide-and-conquer recursion therefore never latches the pool full: as root strands
complete they free permits, deeper sites immediately re-reserve, and the exponential tree keeps
spawning. **F5 (`fib`) stayed at ~1.5M spawns at *every* cap value tested** — the concurrent cap bounds
*simultaneity*, not *cumulative count*. The "emergent hierarchical decline" the pre-impl §2.8.4
described **does not exist**: there is no busy signal that stays latched under a recycling permit pool.

**Consequence (the reversal).** The count collapse is **not** the cap's to deliver, so structural
hierarchical decline (§2.8.4) is **MANDATORY, not optional** (this is what resolves gate G3 by
measurement). The `SPARK_BUDGET` create-gate is retained for exactly what it always bounded —
*concurrent* IVar allocation to `O(cap)`, the memory floor (§3.6.3) — but it is **not** the utilization
mechanism. Gate **G1** (the "~2/core cap multiplier") is moot for count-collapse: the depth counter
(§2.8.4), not the cap, sets utilization. The **reserved-vs-executing gap (G2)** is likewise moot for
the shipped mechanism — the depth bound is a worker-origin thread-local, not a read of the in-flight
count, so no new symbol was needed (`cranelisp_spark_executing_count()` not taken; §2.8.6). The
one-counter ruling (`effect-concurrency.md` §3.1.3, Principle 8) is preserved: `IN_FLIGHT_SPARKS`
stays the single budget counter for the memory floor, and the depth mechanism adds no *counter*, only
a module-private per-strand nesting level.

#### 2.8.4 Hierarchical decline — worker-origin thread-local depth counter (as-built; MANDATORY), and IVar-force backoff

**Invariant.** Once a strand is dispatched it runs its sequential path with **no further sparking
inside its serialized subtree** (0534's core finding: declined-coarse + admitted-fine is strictly the
*worst* outcome). Because the concurrent cap cannot deliver this emergently (§2.8.3), the shipped form
is a **structural depth bound** — this is the count-collapse lever, not an optional refinement.

**Mechanism (as-built — Wave 2e).**
- A **module-private thread-local `SPARK_DEPTH`** tracks the current strand's spark-nesting depth on
  the worker running it.
- At a candidate site, spark is admitted only while `SPARK_DEPTH < MAX_DEPTH`; at or beyond the limit
  the site takes the direct (inline) arm and runs its subtree serially, allocation-free (§3.6.3 floor).
- **Worker-origin with cross-spawn base propagation.** Depth accumulates down the *logical* spark
  tree, not the physical worker. When a strand is spawned, its **base depth is propagated across the
  spawn** so a **stolen child lands at parent + 1**; on entry to a spawned strand's thunk
  (`ivar_spark`'s spawned closure, Rust side) the thread-local is seeded from the propagated base and
  each nested spark increments it. A stolen child therefore inherits its parent's logical depth
  regardless of which worker steals it. (`/review` verified the cross-spawn propagation CORRECT.)
- `MAX_DEPTH` default = `floor(log2(nproc))` (**= 3** on the 10-core measurement host), env override
  `CRANELISP_SPARK_MAX_DEPTH=N`. Intuition: `2^D` leaves of a binary fork tree fills `D` levels ≈ one
  strand per core — the ~2/core utilization target reached **structurally**, not via a busy signal.
- **Total spawn count is now `O(2^MAX_DEPTH) = O(nproc)`, independent of tree size** — the bound the
  concurrent cap could not provide. This collapses F5's ~1.5M spawns to a bounded frontier and, with
  M-static declining the fine cross-section (§2.8.2), collapses F4-hard ~6 orders of magnitude.

**Why depth-allowed worker-origin, not both-paths and not pure worker-only (both measured, both
rejected).**
- **Both-paths** (Wave 2b) incremented depth on the spark arm *and* the inline arm, so an inlined
  subtree also burned the depth budget. Measured **HARMFUL**: it collapsed effective parallelism to a
  **peak of 2** in-flight strands — the inline path exhausted the budget before the spark path could
  fan out, starving the cores. Must not be reintroduced.
- **Pure worker-only decline with no depth allowance** (Wave 2c) was too aggressive — it declined the
  coarse strands that fill cores and made **F3 7.5× slower**.

The shipped form (Wave 2e) is worker-origin decline **with a depth allowance of `D`**: depth advances
only across actual spawns (propagated to stolen children), and up to `D` levels fan out before
inlining. This fills the cores at depth `D` while bounding the count — the F6 3.4× / F5 1.7× result
(top-of-section table).

**IVar-force backoff — bounded wait (Wave 2d; CPU-efficiency hygiene, NOT a wall fix).** As-built,
`ivar_force`'s wait loop (§3.5) for a PENDING/EVALUATING IVar is a **bounded escalation**
`spin → yield_now → sleep`, replacing the previous pure `spin_loop`; `CRANELISP_IVAR_SPIN=1` restores
the old unbounded spin. On decline-heavy shapes where many forcers wait on strands it roughly **halves
CPU** — F3 dropped from **617% → 275%** CPU — at **neutral wall time**. It is **not** a parallelism
win: profiling (S104) showed F3's cost is **contention** (allocator + atomic-RC cache-line traffic),
not spin waste, so freeing the spin-burned cores lowers CPU without moving the wall. Recorded honestly
so the backoff is not mistaken for a speedup — the F3/alloc-RC floor is the set-aside memory class
(§2.8.8). (`/review` verified the backoff CORRECT — no Blocker/Important.)

#### 2.8.5 B4 default-flip (the demoted contention axis)

`SPARK_DENSITY_MAX_DEFAULT` flips **`1 → 0`** this sprint (B4 off by default), per the arch demotion
(`effect-concurrency.md` §3.1.1; the §2.7 demotion banner). Rationale, recorded there and in §2.7:
B4 is *net-harmful* at full cores on this class (112s default-on vs 24s off vs 0.9s serial) because
it declines the coarse D&C sparks while the fine score-0 accessors stay admitted — the incoherent
decline-coarse-while-admitting-nested-fine state. With **M-static** now owning *selection* (the fine
accessors are declined structurally) and **M-dynamic** owning *quantity*, B4 has no role for the
recursion/search class. The §2.7 design is **preserved, not deleted**: the contention-scoring concept
stays valid for the alloc/RC-dense *compute-bound* class (S99 F2 vec-COW) and may return
**Phase-H-composed** (scoring the surviving population the memory mechanisms define). It must never
*default*-fire again in the incoherent state; opt-in `CRANELISP_SPARK_DENSITY_MAX=N` remains as the
Stage-0 B4-on diagnostic row. This is a **constant value change** — no public surface, no cascade.

#### 2.8.6 Codegen seams (for Phase-5 `/dev`) and the unit-scenario space

Each mechanism lands at a named §4 seam; **none touches a public edge** (confirmed below):

- **M-static** — in the sparkability pass (`sparkability.rs`), consumed at `compile_let`'s §4.1
  decision point and `compile_apply`'s §4.4 decision point (and the §4.2 `let` lenient path). The
  recursive-SCC ∧ non-tail predicate replaces/augments `is_worth_sparking` (§2.2) for this class. The
  SCC pass is a backend-internal analysis built once over the loaded call graph (read from
  `ModuleEntry::Def.callees`), cached per compile unit, and read at each candidate site;
  `in_tail_position` is already available at the apply site (§2.5.3). `find_sparkable_bindings` /
  `find_sparkable_args` gain the predicate.
- **M-dynamic / create-gate** — the create-gate emission (§3.6.2) at both sites. **No codegen shape
  change.** As-built it is retained as the **concurrent-memory floor only** (bounds in-flight IVar
  allocation to `O(cap)`), **not** the count-collapse lever — measurement showed the cap does not bound
  cumulative spawns (§2.8.3). The `spark_budget_try_reserve` branch, block structure, join-point, and
  TCO composition are unchanged.
- **Worker-origin depth decline** (as-built; **MANDATORY** — the shipped count-collapse lever, §2.8.4)
  — a module-private **thread-local `SPARK_DEPTH`** seeded on entry to `ivar_spark`'s spawned closure
  (`ivar.rs`, Rust side) with the parent's base depth **propagated across the spawn**, incremented per
  nested spark, and read at the candidate site to force the inline arm once `SPARK_DEPTH ≥ MAX_DEPTH`
  (default `floor(log2(nproc))`, env `CRANELISP_SPARK_MAX_DEPTH`). Module-private, no export.
- **IVar-force backoff** (§2.8.4) — `ivar_force`'s PENDING/EVALUATING wait loop (§3.5) is a bounded
  `spin → yield_now → sleep`; `CRANELISP_IVAR_SPIN=1` restores pure spin. Module-private, no export.
- **B4 default-flip** — the `SPARK_DENSITY_MAX_DEFAULT` constant `1 → 0` in the density-axis site
  (§2.7 / ownership-codegen B4).

**No-new-symbol / no-types-edit — confirmed.** M-static reads the existing Decision-21
`callees` field via backend-internal SCC analysis (no new type, no schema/baseline cascade).
M-dynamic reuses `cranelisp_spark_budget_try_reserve` + `IN_FLIGHT_SPARKS` (no new export). The
worker-origin `SPARK_DEPTH` counter and the `ivar_force` backoff loop are module-private thread-local /
loop logic (no export). The B4 flip is a constant value. Therefore: **no backend `public-api.txt` diff,
no `cranelisp-intrinsics` `public-api.txt` diff, no `cranelisp-types` edit** — the baseline-diff
discipline is not triggered by this design, and the as-built landing confirmed it (SPRINT.md: "no API
change"). Gate G2's last-resort `cranelisp_spark_executing_count()` was **not needed** as-built.

**Unit-scenario space the implementation must cover** (Phase-5 `/dev`; feeds `/qa`'s Stage-0 matrix;
mirrors §9's sparkability/gate tiers):

- **Recursion-SCC classification — {recursive, non-recursive} × {tail, non-tail}** (the M-static
  discrimination, §2.8.2's table as fixtures): self-recursive `fib` (recursive/non-tail → **spark**);
  mutual recursion `a→b→a` (recursive-SCC>1/non-tail → **spark**); flat `cell-at` accessor
  (non-recursive/non-tail → **decline**); tail-recursive accumulator loop (recursive/tail → decline);
  flat call in tail position (non-recursive/tail → decline). Plus: unloaded/unresolved callee →
  treated non-recursive → decline (soundness-toward-decline).
- **Depth-decline boundary** (the as-built count-collapse lever): a candidate sparks while
  `SPARK_DEPTH < MAX_DEPTH` and inlines at `≥ MAX_DEPTH`; a **stolen child observes `parent + 1`**
  (cross-spawn base propagation), not the stealing worker's own depth; `CRANELISP_SPARK_MAX_DEPTH`
  raises/lowers the bound. **Regression guards:** both-paths depth accounting must NOT be reintroduced
  (collapses to peak-2, §2.8.4); `MAX_DEPTH` beyond ~`log2(cap)` re-explodes spawns (budget-inline
  ceiling, §2.8.8) — the D=3 default stays under it.
- **Create-gate memory floor** (unchanged shape; now the memory bound, not the utilization gate):
  `IN_FLIGHT_SPARKS = cap−1` → next candidate sparks; `= cap` → inlines — the §3.6.1 `try_reserve`
  all-or-nothing property.
- **IVar-force backoff**: a decline-heavy shape holds neutral wall under `CRANELISP_IVAR_SPIN=1` vs the
  bounded default while CPU drops (§2.8.4); no behavioural divergence between the two (spin-vs-backoff
  is a scheduling choice only).
- **B4-off byte-identity when facts absent**: with `SPARK_DENSITY_MAX_DEFAULT = 0` the density axis is
  inert and admission is byte-for-byte the pre-B4 admission — confirm no density-decline fires (the
  §2.7 activation-gating property with the default now disabling).

Cross-refs: `effect-concurrency.md` §3.1.1 (thesis / axis re-ranking), §3.1.2 (M-static no
interface), §3.1.3 (counter unification / no third throttle), §3.1.4 (orthogonality + roadmap
correction).

##### Gate dispositions (S104 — measurement resolved most; the routed originals are kept for the record)

- **G1 — M-dynamic cap multiplier — MOOT (resolved by measurement).** The concurrent cap does not bound
  cumulative spawns (§2.8.3), so the "~2/core cap value" is not the utilization knob. Utilization is set
  *structurally* by `MAX_DEPTH` (default `floor(log2(nproc)) = 3`, env `CRANELISP_SPARK_MAX_DEPTH`); the
  cap remains the memory floor at its existing default.
- **G2 — reserved-vs-executing — MOOT for the shipped mechanism.** The depth bound is a worker-origin
  thread-local and does not read the in-flight count, so the reserved-vs-executing gap is off the
  count-collapse path. No new symbol was taken (`cranelisp_spark_executing_count()` not needed).
- **G3 — emergent vs structural hierarchical decline — RESOLVED: structural, MANDATORY.** The emergent
  (busy-signal) form does not exist under a recycling permit pool (§2.8.3); the worker-origin
  `SPARK_DEPTH` counter (§2.8.4) is the shipped, required mechanism. A both-paths variant was measured
  harmful (peak-2); pure worker-only with no allowance made F3 7.5× slower; worker-origin
  **depth-allowed** decline is the shipped form.
- **G4 — the f3 / B4-off trade — STILL OPEN, folded into the S105 focus (§2.8.8).** B4 default-off loses
  f3's S102-recorded −82% N-worker benefit for the alloc/RC-dense class; f3 still meets the north-star
  bar (B4-off ≈ toggle-off). This is the *same* limit §2.8.8 records — the uniform depth allowance can't
  distinguish alloc-free from alloc-heavy fan-out. **S105 reclamation:** the demoted B4 density signal
  returns as the *depth-gate input* (deep for alloc-free, shallow for alloc-heavy), **not** the old
  admission-decline form. Cross-ref FIXME 0535.

#### 2.8.7 Measurement strategy (the S104 doctrine)

**Problem.** The utilization mechanisms above (M-static selection, M-dynamic ~2/core cap, the
depth-allowance hierarchical decline) are all *order-of-magnitude* levers — they move a workload
from 100×-serial to ~serial, or from serial to ~3×. Chasing that class of win with a
rigorous statistical harness (fixed rep counts, idle-guards, thread-count sweeps) is the wrong
instrument, and this sprint proved it does active harm. Two failure modes, both observed at S104:

- **The idle-guard self-defeats mid-sweep.** A harness that refuses to time a rep until the
  machine is idle cannot sweep: the sweep's *own* prior reps (and the parallel worker load they
  generate) keep the machine busy, so the guard either blocks forever or admits reps under exactly
  the contention it was meant to exclude. The guard invalidates the very series it gates.
- **`CRANELISP_SPARK_STATS` inflates the wall it is meant to explain.** Under hierarchical decline
  the per-declined-site counter (`SPARK_SERIAL_CONTINUES`) fires **hundreds of millions of times**
  — once per inlined nested candidate across an exponential recursion. Even a single relaxed atomic
  at that rate dominates the wall: it made F5 read **5.8 s** with stats on versus the real **0.7 s**
  with stats off — an ~8× pure measurement artifact. Timing a wall with stats enabled measures the
  instrument, not the mechanism.

**Doctrine (S104, user-directed).** When chasing an order-of-magnitude win, measure **single-shot**:
`T = nproc`, **one rep**, wall-clock plus a single cheap counter — not a rep/idle-guard/sweep
harness. Specifically:

1. **Time the wall with `CRANELISP_SPARK_STATS` OFF.** The stats atomics are a separate concern from
   the wall; enabling them corrupts the number you are trying to read.
2. **Get spawn / peak-executing counts from a SEPARATE stats-on run.** Counts and wall are two
   different measurements of two different runs; never read both from one process. The count run's
   wall is meaningless (see the 8× artifact); the wall run's counts do not exist.
3. **Check `load1` is low before timing.** A single-shot wall has no averaging to hide a busy
   machine, so confirm the host is quiet (`uptime` load-average near zero) immediately before the
   timed run — this replaces the self-defeating idle-guard with an external precondition check.
4. **Reserve the rigorous harness for final acceptance only.** `tests/perf/s104_utilization.py`
   (rep counts, thread sweep, statistics) is the *acceptance* instrument — run it once, at the end,
   to confirm the shipped default clears the north-star bar. It is not the exploration instrument.

**The reproducible instrument.** The F1–F6 fixtures (`tests/perf/` + the §9 sparkability/gate
tiers) plus the M-static discrimination experiment (§2.8.2's {recursive, non-recursive} ×
{tail, non-tail} table as fixtures) are the reproducible measurement surface: each isolates one
axis (F1 coarse-parallel, F4/F3 alloc-RC-dense, F5 deep-recursion count, F6 balanced alloc-free
compute), so a single-shot wall + a stats-on count run on the relevant fixture attributes a change
to its mechanism. Cross-ref: `effect-concurrency.md` §3.1 (the axis model these fixtures probe).

**S105 fidelity uplift — the finer instruments this doctrine now needs.** Attributing the
post-inc-II F3/F4 *residual* (~2.6×) is a **decomposition** problem, not a wall-precision one
(`effect-concurrency.md` §3.1.6; `tests/plan/s105-residual-attribution.md`), so it wants *finer
instruments*, not more reps — but the S104 doctrine above is preserved intact (wall with all
counters OFF; counts from a separate run; HW counters external; no self-defeating idle-guard). The
four NEW gated attribution seams `/qa` named — **N1** per-run alloc-bytes, **N2** per-branch/per-site
alloc attribution, **N3** per-site residual-atomic-RC dump, **N4** the FINE stack-oracle env gate
(`CRANELISP_NO_STACK_ALLOC`) — are specified where their mechanisms live, in
`ownership-codegen.md` §13.2.2 (RC/alloc counters extend the §13.2.1 `[RC_STATS]` family; N4
relocates the §4 `STACK_ALLOC_ESCAPE_FACT_SOUND` gate to a runtime env read). Each is zero-cost-off,
intrinsics/backend-internal, and needs no `cranelisp-types`/public-API/C-ABI change (§3.1.6-R5). The
recommendation on N4-vs-a-two-build-fallback (for the Phase-4 wave gate) and the `STACK_SLOT_HITS`
backend-side-read boundary (the h2-RED counter-surface seam stays un-force-resolved) are recorded
there, not duplicated here.

#### 2.8.8 Remaining problems / open work

The S104 mechanisms deliver the utilization-axis win (F6 balanced compute → ~3.4×; F5 deep recursion
collapsed to `O(2^D)` spawns; the never-slower-than-serial floor held for the count-explosion class).
Four problems remain open and are recorded here as the durable statement of what is left. All are
cross-referenced to `effect-concurrency.md` §3.1 (the utilization-axis vs. contention-axis split).

- **S105 focus — density-aware depth allowance.** The depth knob (`SPARK_MAX_DEPTH`) is a *single*
  scalar: it fans the top `D` levels out and inlines below, blind to what the fanned-out strands
  *do*. But the two classes it must serve pull in opposite directions: an alloc-free compute fan-out
  (F6) *parallelizes* — deeper is better (measured 3.4× at D=3) — while an alloc-heavy contended
  fan-out (F4/F3) *contends* on leaf refcount traffic — deeper drives it further above serial. A
  single depth cannot be right for both. The fix is to gate depth on the **allocation/RC-density
  signal** the ownership-inference read path already supplies (§2.7, the demoted B4 axis): *deep*
  allowance for alloc-free strands, *shallow* (≈1) for alloc-heavy ones. This is the **synthesis of
  the S104 utilization axis with the §3.1 contention axis** — the two axes composed rather than one
  demoted — and is the S105 focus. Cross-ref: `effect-concurrency.md` §3.1.1 (axis re-ranking),
  §2.7 (the density signal, preserved for this reuse).

- **Budget-inline depth-leak ceiling (needs a backend hook).** The create-gate's inline/direct arm
  advances **no** `SPARK_DEPTH` — it is emitted codegen with no runtime hook into the depth counter
  (which only moves at `ivar_force` boundaries). So a create-gate site declined for *budget* reasons
  (`IN_FLIGHT_SPARKS` at cap, not depth spent) direct-calls its child at the **same** fork-depth; a
  deep recursion budget-inlined shallow then re-sparks via permit-recycle at that shallow depth. This
  caps the usable depth allowance at `D ≈ log2(cap)`: above it the fan-out approaches the concurrent
  cap before the depth cutoff bites, and the leak re-opens (measured: F5 re-explodes to **1.3M
  spawns at D=4** on a 10-core host, vs. 14 spawns at D=3). The shipped **D=3 default sits safely
  under** this ceiling (`2^3 = 8 ≤ nproc ≤ cap/2`), so it is a bounded ceiling, not a live defect —
  but raising `D` for a deeper compute fan-out (the density-aware work above) first requires a
  **backend hook that advances `SPARK_DEPTH` on the inline arm**, which cannot be closed in the
  runtime alone (§2.8.4). Cross-ref: `effect-concurrency.md` §3.1.3 (counter unification).

- **Alloc/RC-contention floor (F3, F4-hard) stays above serial.** The genuinely alloc/RC-dense
  compute-bound class remains **above serial** even after the S104 cures, because its dominant cost is
  in-leaf vec-COW leaf-refcount traffic bouncing across cores — a **memory-model** cost, not a
  scheduler one. This is the deliberately-set-aside class: it is cured by the density signal (above) +
  the **Phase-H** memory work (owned-copy mutate-in-place / non-atomic thread-local RC), **not** by
  any create-gate or depth lever. Recording it here so it is not mistaken for an S104 regression.
  Cross-ref: `effect-concurrency.md` §3.1 (contention axis is Phase-H), §3.6.3, §2.6.

- **F4-at-D3 floor trade (accepted).** The shipped `D=3` default **regresses F4-hard relative to
  `D=1`**: a deeper allowance fans F4's alloc-heavy tree out further, and (per the contention floor
  above) that costs it. This was **accepted by the user (2026-07-07)** as the price of the F6
  compute-parallel win (`D=1` would forfeit F6's 3.4× to protect an F4 class that is a Phase-H target
  regardless). It is a conscious axis trade, not an oversight; the density-aware allowance (S105
  focus) is what dissolves it — `D` deep for F6, shallow for F4 — so the trade is transitional.
  Cross-ref: `effect-concurrency.md` §3.1.1.

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
> **The STATIC axis is now designed — §2.7** (S102; consumes the ownership-inference per-site
> facts; implementation rides increment I as ownership-codegen §13.2 ladder entry B4).

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
- A `par-map` / parallel benchmark showing near-linear speedup to N cores for ≥1µs/element work; observational equivalence with the serial result; **never slower than serial** *for allocation-/RC-light branches* (the spark-machinery floor, per the §2.6.2/§3.6.3 scope notes — the ≥2 gate + cost heuristic must keep cheap work on the sequential path; allocation-/RC-heavy branches are covered only once the §2.7 density axis + the Phase-H memory-model mechanisms land).

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
  never slower than serial (the §2.6.2 **spark-machinery** floor — scope per the §2.6.2
  note; allocation-/RC-heavy shapes are out of this test's scope until §2.7 lands).
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
