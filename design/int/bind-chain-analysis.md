# Bind Chain Independence Analysis

Post-expansion, pre-typecheck pass that transforms `bind!`-expanded AST trees into `Expr::ParBind` nodes for automatic IO scheduling.

## References

- `spec/10-io.md` §10.12 — Automatic IO Scheduling
- `sprints/SPRINT.md` — Sprint 85 plan (the wiring sprint; §Scope item 1, §"Architecture review (Phase 2)" (a))
- `design/arch/fixmes/0367-int-resource-serial-scheduling-not-wired.md` — the driving FIXME
- `sketch/src/schedule.rs` — prototype independence analysis (367 lines)
- `crates/cranelisp-platform/src/lib.rs` — `SchedulingClass` enum, `PlatformFn.scheduling_class`
- `design/int/io-integration.md` — platform DLL loading and registration
- `crates/cranelisp-types/src/ast.rs` — `Expr::ParBind` variant

---

## 1. Problem Statement

The spec (§10.12) requires the compiler to automatically parallelise data-independent, commutative IO effects in `bind!` chains. There is no `par-bind!` form — concurrent IO is transparent to the programmer.

The `bind!` macro expands `(bind! [x (e1) y (e2)] body)` into nested `bind`/`fn` forms:

```
(bind e1 (fn [x] (bind e2 (fn [y] body))))
```

After macro expansion and AST building, this appears as nested `Expr::Apply` nodes calling `bind` with lambdas. This pass must:

1. Recognise the nested bind pattern in the expanded AST.
2. Collect the flat chain of `(name, io_expr)` bindings.
3. Determine which bindings are data-independent and call non-Sequential platform functions.
4. Group eligible bindings into `Expr::ParBind` nodes.
5. Leave ineligible bindings as regular sequential bind calls.

The result is an AST where parallelisable IO groups are explicit, enabling the backend to emit `Par` nodes (tag=3) and the trampoline to dispatch them concurrently.

---

## 2. Input / Output

### Input

- **Expanded AST** (`Program`, i.e. `Vec<TopLevel>`): the output of macro expansion and AST building, before typechecking. Bind chains appear as nested `Expr::Apply(Var("bind"), [io_expr, Lambda([name], body)])`.
- **Scheduling class registry** (`HashMap<String, SchedulingClass>`): maps platform function names to their scheduling class, populated during DLL loading (see §4 below).

### Output

- **Transformed AST** (`Vec<TopLevel>`): same structure, but eligible sequences of bind steps are rewritten as `Expr::ParBind { bindings, body, span }` nodes. Non-eligible steps remain as regular `Expr::Apply` bind calls. The transformation is semantically transparent — typechecking and execution produce the same results whether or not parallelisation occurs.

### Invariants

- A `ParBind` node always contains ≥2 bindings. Single-binding groups are demoted back to sequential bind calls (no overhead for trivial cases).
- The pass is recursive: bind chains nested inside lambdas, match arms, or let bodies are also transformed.
- The pass is idempotent: running it twice produces the same result.

---

## 3. Algorithm

The algorithm follows the sketch's `schedule.rs` structure with minor naming adjustments.

### 3.1 Pattern Recognition

A bind chain starts with an expression matching:

```
Expr::Apply {
    callee: Expr::Var { name: "bind" | "*/bind" },
    args: [io_expr, Expr::Lambda { params: [name], body }],
}
```

The `is_bind_chain_start()` function checks this pattern. The check matches any callee name that is exactly `bind` or ends with `/bind` (e.g., `core.io/bind`). This is not a glob pattern — it is a suffix match using `name.ends_with("/bind")`. This handles both bare `bind` (imported) and qualified `platform.stdio/bind` style references.

### 3.2 Chain Collection

`collect_bind_chain(expr)` recursively flattens nested bind forms into a flat vector:

```
[(name1, io_expr1, span1), (name2, io_expr2, span2), ...], final_body
```

This walks the nested structure: each bind's lambda body is either another bind (continue collecting) or the terminal body expression.

### 3.3 Scheduling Classification

For each `io_expr` in the chain, `classify_expr()` determines the scheduling class:

1. If `io_expr` is `Apply(Var(name), ...)`, look up `name` in the scheduling class registry.
2. Try bare name first, then strip module prefix (`platform.stdio/print` → `print`).
3. Default to `Sequential` for any expression that is not a direct platform function call (function composition, nested binds, let expressions, etc. are conservatively sequential).

This conservative approach means only direct calls to platform functions with known scheduling classes are eligible for parallelisation. Wrapper functions that call platform functions are treated as sequential — the analysis does not chase through function bodies.

### 3.4 Data Independence Check

Two bindings `(xi, ei)` and `(xj, ej)` are data-independent when:

- `xi` does not appear free in `ej`
- `xj` does not appear free in `ei`

The pass checks this incrementally: for each binding in the chain, it checks whether the binding's `io_expr` uses any name bound by prior steps (both already-committed sequential steps and the current parallel group candidates). This is a conservative approximation — it only tracks names explicitly bound in the bind chain, not all possible aliases.

`free_vars(expr, globals)` computes the set of free variable names in an expression. The same function used by the sketch's `captures.rs` module is available in the reimplementation's backend crate. Since this pass runs in the binary crate (not the backend), the free variable analysis must either:

- **Option A**: Be duplicated or extracted into `cranelisp-types` (which has no dependencies).
- **Option B**: Be placed in a shared utility crate.
- **Option C (recommended)**: Be placed in `cranelisp-frontend`, which already depends on `cranelisp-types` and is a natural home for AST analysis utilities. The backend can also depend on frontend for this function, or the function can be duplicated if the dependency is undesirable.

**Decision**: Place `free_vars_expr()` in `cranelisp-types` as a method or free function, since `Expr` is defined there and the analysis is pure AST traversal with no external dependencies. This avoids adding a frontend→backend or backend→frontend dependency.

### 3.5 Grouping

The chain is scanned left to right. A running "parallel group" accumulates consecutive bindings that are:

1. Non-Sequential (Commutative or ResourceSerial), AND
2. Data-independent of all previously bound names (both committed and in the current group).

When a binding fails either condition, the current parallel group is flushed:

- **≥2 entries**: emit a `Segment::Parallel` (becomes `Expr::ParBind`)
- **1 entry**: demote to `Segment::Sequential` (stays as regular bind)
- **0 entries**: no-op

The failing binding itself is emitted as `Segment::Sequential`.

After scanning the full chain, any remaining parallel group is flushed.

### 3.6 Reconstruction

The segments are folded right-to-left (innermost first) to rebuild the nested expression:

- `Segment::Sequential(name, io_expr, span)` → reconstruct `Expr::Apply(bind, [io_expr, Lambda([name], inner)])`
- `Segment::Parallel(bindings)` → `Expr::ParBind { bindings, body: inner, span }`

Sub-expressions within each binding's `io_expr` and the final body are recursively transformed by the same pass (to handle nested bind chains inside lambdas, match arms, etc.).

### 3.7 Launch-and-continue emission (S96 Chunk B, spec §10.12.7)

The SAME pass also emits `Expr::LaunchContinue` — the marker for a **detached**
effect (a fire-and-forget strand with no join point), the backend counterpart of
which is the `IO_TAG_LAUNCH` node (`design/backend/io-trampoline.md §15`). This is
a small discriminator layered on top of the existing grouping cores (Principle 7 —
the token-disjointness core is NOT forked).

**Where it fires.** In `rebuild_chain`'s right-to-left reconstruction, at the
`Segment::Sequential` arm — i.e. a bind step that did **not** join a parallel group
(a lone schedulable step, or one demoted from a 1-element group). Par-grouped
segments (`Segment::Parallel` → `ParBind`) are never relowered as launch: a launch
is a **single launched arm** (the §10.12.7 discriminator), while `ParBind` is the
structured-join of ≥2 arms.

**Eligibility predicate (E1–E3 — the single-step arm runs the SAME check as the
sub-tree arm; FIXME 0478).** A `Segment::Sequential(name, io_expr, …)` with
continuation `result` lowers to `Expr::LaunchContinue { launched: io_expr,
continuation: result }` iff ALL of (the local, sound, conservative predicate
`effect-concurrency.md §4.1` pins for **both** the single-step and the discarded-
sub-tree arms):

1. **(E1) Result discarded** — `name` does not appear free in the continuation
   (`!free_vars_expr(&result).contains(&name)`). This reuses the `free_vars_expr`
   independence core (§3.4), applied to the CONTINUATION (the §10.12.7 "result is
   discarded" criterion). The launched effect's result is unused downstream.
2. **(E2) Value-locality — the launched step shares no free variable with the
   continuation** (`free_vars_expr(&io_expr).is_disjoint_from(free_vars_expr(&result))`,
   modulo globals). **This is the check the single-step arm was MISSING (FIXME 0478)** —
   the sub-tree arm runs it (over the sub-tree's combined free vars); the single-step
   arm did not, so a **discarded `ResourceSerial` middle step whose continuation
   performs a same-token effect on the same handle** could be detached, reordering two
   same-token effects across the detach boundary. Concretely: a step
   `(_ (send-conn conn r1))` whose continuation does `(send-conn conn r2)` shares the
   free var `conn` — same per-value handle ⇒ same dynamic token ⇒ detaching reorders.
   E2 refuses it (shared `conn`). The disjointness *witnesses* token-locality without
   resolving concrete tokens (runtime/dynamic, §5/§8.1): a launched effect whose
   resource value does **not** also flow into the continuation cannot ride the same
   per-value token as a continuation effect. (For the legitimate accept-loop launch the
   handler's `conn` is bound *inside* the launched sub-tree and is absent from the
   continuation — E2 passes; that path is unchanged.)
3. **(E3) No shared-singleton-token effect — `ResourceSerial` only, refuse
   `Commutative` (token-0) and `Sequential` (token-1).** Tightens the prior
   `classify_expr(io_expr) != Sequential` test (which admitted **both** `Commutative`
   and `ResourceSerial`): a `Commutative` (token-0) or `Sequential` (token-1) effect
   rides a **shared singleton** token whose disjointness E2's value-provenance argument
   cannot witness — two strands on token-0 (a shared-`stdout` `print`) interleave
   observably, and the per-token semaphore gives exclusion but not source-order across
   the detach boundary, so a wrongly-detached shared-token step *reorders*. For an
   **inferred** (un-annotated) detachment the disposition is **REFUSE**. The one
   permitted non-`ResourceSerial` member is a resource-free `sleep` timer — but **only
   as a sub-tree member, never as the single-step root** (`is_sleep_timer_leaf`,
   `effect-concurrency.md §4.1` timer refinement); the single-step arm keeps refusing a
   lone `sleep`. Per **Gap G2** the analysis approximates "tokens disjoint" by
   scheduling class + value-shape (it does NOT statically resolve concrete tokens — the
   trampoline owns the live token decision).

> **DECOUPLED from the ABI v9 descriptor cut (S97).** This hardening is a **compile-time
> inference-soundness** fix over AST free-variable provenance + scheduling class — it
> touches **no** runtime descriptor representation and is **sound under both v8 and v9**.
> v9 (`effect-concurrency.md §4.1.1`) *strengthens E2's grounding* (the disjoint token
> literally rides inside the freshly-bound handle's header) but **does not change the
> check**. So 0478 **must NOT be gated on the v9 reshape's schedule** — it can land in any
> change-set, before or after v9. (`/arch` re-classed it from a §B v9 fold to "co-located
> but decoupled," SPRINT.md §"Architecture review (Phase 2)" Fold verdict.)

**Conservative-`Bind` fallthrough (the sound default).** When NOT provably
eligible — the result is **used** downstream, OR the effect is `Sequential`-class —
the step lowers as an ordinary sequential `Bind` (`make_bind`), exactly as before.
Declining to detach is always sound (§10.12.7: "whether a given eligible effect is
run detached … is implementation-determined"), so the non-launch path is the safe
default and the launch path is opt-in by eligibility, never the fallback.

**Idempotency.** `recurse_children` handles a pre-existing `Expr::LaunchContinue`
by recursing both sub-trees without re-grouping (the `ParBind` precedent, §5.2), so
the retry-from-top property is preserved.

---

## 4. Platform Scheduling Data Access

### Data Flow

The scheduling class registry must be available to the bind chain analysis pass. The data originates from platform DLL manifests:

```
DLL manifest → OwnedPlatformFnDescriptor.scheduling_class
  → registered during load_and_register_platform()
    → stored in ???
      → passed to bind chain analysis
```

The sketch stores this in `TypeChecker.platform_scheduling: HashMap<String, SchedulingClass>` and provides `tc.scheduling_of(name)`. The reimplementation's typechecker does not currently have this field.

### Design

Add a `platform_scheduling: HashMap<Symbol, SchedulingClass>` field to the `CompilationSession` (not the typechecker — the scheduling class is a pipeline concern, not a type system concern). This keeps the typechecker crate free of platform dependencies.

The field is populated during platform DLL loading in `load_and_register_platform()` (already called in `compile_graph_only()` before module compilation begins). Each descriptor's `(name, scheduling_class)` pair is inserted.

The bind chain analysis pass receives a `&HashMap<Symbol, SchedulingClass>` (or a wrapper with a `scheduling_of(name) -> SchedulingClass` method) when invoked.

**Alternative considered**: Store in `TypeChecker` as the sketch does. Rejected because the typechecker crate (`cranelisp-typecheck`) should not depend on `cranelisp-platform` for a single enum. The scheduling class is only used by this pass, which lives in the binary crate.

**Alternative considered**: Pass the full `OwnedPlatformFnDescriptor` list. Rejected because only the scheduling class is needed, and the descriptors may not be retained after loading.

### Lookup Logic

```rust
fn scheduling_of(
    registry: &HashMap<Symbol, SchedulingClass>,
    name: &str,
) -> SchedulingClass {
    // Direct lookup (bare name after import).
    if let Some(sc) = registry.get(name) {
        if *sc != SchedulingClass::Sequential {
            return *sc;
        }
    }
    // Qualified name fallback: "platform.stdio/print" → "print".
    if let Some(pos) = name.rfind('/') {
        if let Some(sc) = registry.get(&name[pos + 1..]) {
            return *sc;
        }
    }
    SchedulingClass::Sequential
}
```

This matches the sketch's `classify_expr` approach. The function strips module qualifiers because bind chain expressions may reference platform functions by their qualified import name.

---

## 5. Pipeline Insertion Point (S84 design → S85 implementation-ready)

> **Status (S85 Phase 3, FIXME 0367 — implementation-ready).** The S84 rewrite
> below specified the live wiring seam against the post-S78 in-call-stack cluster
> orchestration. **S85 is the implementation sprint.** The S85 `/arch` Phase-2
> review (`sprints/SPRINT.md` §"Architecture review (Phase 2)" (a), 2026-06-17,
> APPROVE-WITH-REVISIONS) **confirmed** this seam verbatim and **closed the one
> open `/dev` choice the S84 draft left hedged** — the `SymbolTable` generic
> reconciliation (§5.3 step 3) is now a *decided* design point, not a "/dev's
> call": **genericize the entry fn over `<C, L>`** (the `&SymbolTable`-view
> alternative is retained only as a fallback if genericization snags). `/arch`
> further confirmed **no `cranelisp-types` / cross-crate change** is required
> anywhere in S85 — the reconciliation is entirely int-side. The prior batch-mode
> / simple-batch / REPL three-flow design (`compile_single_module`,
> `compile_and_run`, the `ReplInput::Defn` hook) is **stale** — those entry
> points were retired by the S78 restructure (`design/int/s77-int-restructure.md`,
> `s78-entry-module.md`). The pass is `#[allow(dead_code)]`
> (`apply_bind_chain_analysis`, `src/session_setup.rs:328`, zero live callers;
> `auto_schedule_defn`, `src/bind_chain_analysis.rs:41`). §5.3 below is the binding
> design; §5.4–§5.5 (older prose) are retained as historical context only.

### 5.1 The single live seam — inside `process_cluster_once`, before `check_program_compat`

The post-S78 pipeline has **one** orchestration core that ALL three modes drive:
`process_form::process_cluster_once` (`src/process_form.rs:852`). Both the worker
entry (`cluster::process_cluster`, `ModuleStrategy::Replace` — `--run` / `--link`)
and the REPL eval entry (`eval.rs::process_form_cluster` → `process_cluster_once`,
`ModuleStrategy::Additive`) flow through it. This single-core property is what makes
PO-0367.2 (mode uniformity) **structural**: wiring the pass at one point in
`process_cluster_once` covers `--run`, `--link`, and REPL eval by construction —
there is no second path to keep in sync, and no mode can silently skip it (the
current dormant state is exactly a mode-uniformity hole; the fix closes it at the
one place that all modes share).

**The correct seam is `finalize_cluster`, immediately BEFORE `check_program_compat`
(`src/process_form.rs:1060`), operating on the post-Pass-2-expansion
`expanded_program`** — NOT the pre-expansion `program` built at line 947.

**Why `expanded_program`, not `program`.** `bind!` is a macro. The bind-chain
shape the pass recognises (`Apply(Var("bind"), [io_expr, Lambda([name], body)])`,
§3.1) does not exist in source — it is produced by `bind!` macro expansion. In the
post-S78 pipeline, **macro expansion happens in Pass 2**
(`pass2_check_bodies_with_expansion`, `src/process_form.rs:961`), which populates
`expanded_program` (extended at `:1402`). The pre-expansion `program` at line 947 is
the *regular non-macro* forms only, with `bind!` still unexpanded — so transforming
it would see no bind chains. The algorithm's stated requirement ("after AST build /
macro expansion, before typecheck") maps, post-S78, to: **after Pass 2 builds
`expanded_program`, before `finalize_cluster` calls `check_program_compat`.** This is
the load-bearing correction over the stale §5.4 design, which assumed a
`build_program` flow where `bind!` was already expanded at build time.

### 5.2 Exact call-order constraint

In `finalize_cluster` (`src/process_form.rs:1043`) the current order is:

```
1049  let mut final_working = wrap_exprs_as_defns(expanded_program);
1056  for defn in &accumulator.default_method_defns { final_working.push(...) }
1060  let (maybe_gap, cluster_warnings) = check_program_compat(.., &final_working)?;
```

The pass is invoked **between line 1058 and line 1060** — over `final_working`
(the wrapped `expanded_program` plus appended default-method defns), after the
defaults are appended and BEFORE `check_program_compat`. Rationale for "over
`final_working`, after defaults appended":

- The pass MUST run before typecheck because `ParBind` is a distinct `Expr`
  variant the typechecker must see (it infers the bindings' types and the body).
  Transforming after typecheck would leave the inferred types stale.
- Running over `final_working` (rather than `expanded_program` directly) folds the
  default-method defns into the same transform sweep — a default method body may
  itself contain a `bind!` chain. `wrap_exprs_as_defns` has already lifted bare
  top-level exprs into defns, so a single `for defn in &mut final_working` sweep
  (the `apply_bind_chain_analysis` shape, §5.3) covers every body uniformly.

**Idempotency under retry-from-top.** `finalize_cluster` can run MULTIPLE times for
one cluster: an FQ-auto-load gap (`check_program_compat` returns `Some(gap)` at `:1067`,
`finalize_cluster` returns `ClusterOnce::Gap { dep }` at `:1074`) and the cluster
**retries from the top** against larger live state (`s78-entry-module.md` §3). Each
retry rebuilds `expanded_program` fresh from `sexps` (Pass 2 re-runs) and calls
`finalize_cluster` again. The pass MUST therefore be **idempotent** — running it on
an already-`ParBind`-transformed tree must produce the same tree. This holds: the
pass rebuilds `expanded_program` from scratch each pass (it is never mutated in place
across retries — `expanded_program` is a fresh `Vec` per `process_cluster_once`
invocation, `:862`), and `recurse_children` already handles a pre-existing
`Expr::ParBind` node (`bind_chain_analysis.rs:467`) by recursing its children without
re-grouping. The §2 "idempotent" invariant is thus preserved by construction — no new
work is required, but the retry-from-top property makes it a **hard correctness
requirement**, not a nicety. Flag: this is the one interaction the wiring must not
break; the unit tests in §8.1 must include an "apply twice = apply once" assertion.

**Seam ordering — the pass never double-applies in practice.** Note the precise
ordering at the seam: (1) `finalize_cluster` builds `final_working`; (2) **the pass
runs on `final_working`**; (3) `check_program_compat` runs and MAY return a gap; (4) on
a gap, `finalize_cluster` returns `ClusterOnce::Gap` and **`final_working` is dropped
unread** — it is a stack local, never stored. The next retry enters a *new*
`process_cluster_once` frame with a *new* `expanded_program` and a *new* `final_working`,
on which the pass runs once. So across the whole retry sequence the pass is applied
**once per surviving `final_working`**, never to its own prior output — the transformed
tree from a gapped attempt is discarded, not fed back in. The idempotency requirement is
therefore a *defence-in-depth* guarantee (and a contract for any future caller that
might reuse a transformed tree), not a property the current retry path actually
exercises. Either way the `:467` `recurse_children` ParBind arm makes re-application a
no-op, so even an accidental double-apply at the seam would be sound.

### 5.3 The entry function and dropping `#[allow(dead_code)]`

`apply_bind_chain_analysis` (doc-comment `src/session_setup.rs:327`; `#[allow(dead_code)]`
at `:328`; `pub(crate) fn` at `:329`) is the correct entry shape — it already iterates
`Defn` and `TraitImpl` method bodies, calling `auto_schedule_defn` per body. The wiring:

1. **Drop `#[allow(dead_code)]`** on `apply_bind_chain_analysis` (`:328`). Once it
   has a live caller the lint is satisfied; keeping the attribute would mask a future
   accidental disconnection. (The three `auto_schedule_expr*` helpers and
   `scheduling_of` in `bind_chain_analysis.rs` stay `#[allow(dead_code)]` — they are
   not on this path; `auto_schedule_defn` is the only live entry and is already
   un-attributed.)
2. **Call it from `finalize_cluster`** (`src/process_form.rs:1043`), between the
   default-method append loop (ends `:1058`) and `check_program_compat` (`:1060`),
   inside the env-flag gate (§5c):
   `crate::session_setup::apply_bind_chain_analysis(&mut final_working, ctx.symbol_tables, module)`.
   `final_working` is already a `let mut` at `:1049`; `ctx: &mut ModuleCompiler` exposes
   `ctx.symbol_tables` (the `&DashMap<ModuleFullPath, SessionSymbolTable>`, the same value
   passed to `check_program_compat` at `:1061`); `module: &ModuleFullPath` is the
   second `finalize_cluster` param. No new value needs to be plumbed into
   `finalize_cluster` — all three arguments are already in scope at the seam.
3. **Generic reconciliation (S85 /arch DECIDED — genericize over `<C, L>`).** The
   type mismatch is real and must be resolved in the change-set: `apply_bind_chain_analysis`
   (`src/session_setup.rs:329`) and the whole `bind_chain_analysis.rs` lookup chain are
   pinned to the **default `<(), ()>`** `SymbolTable`, but `ctx.symbol_tables` is
   `&DashMap<ModuleFullPath, crate::code::SessionSymbolTable>` where
   `SessionSymbolTable = SymbolTable<Code, ()>` (`src/code.rs:19`). The compiler will
   NOT coerce `DashMap<_, SymbolTable<Code, ()>>` to `&DashMap<_, SymbolTable<(), ()>>`
   (invariant in `C`). **Resolution (decided): genericize the lookup chain over the
   table's store params.** This is sound because the pass reads ONLY `C`-independent
   fields:

   - `ModuleEntry::Def { kind, .. }` → matches `DefKind::PlatformEffect { scheduling_class, .. }`
     (`bind_chain_analysis.rs:227`). `DefKind` is **not** parameterised by `C`; the
     `code: Option<C>` field on the `Def` variant is never touched.
   - `ModuleEntry::Import { source, .. }` → follows `source.module` / `source.symbol`
     (`bind_chain_analysis.rs:234`). `ImportSource` is `C`-independent.

   **Precise signature change** (the `SymbolTables` alias at `bind_chain_analysis.rs:31`
   is the single chokepoint — every read fn threads `&SymbolTables`):

   ```rust
   // bind_chain_analysis.rs — generic alias replacing the `<(),()>`-pinned one.
   // CodeStore / LinkerStore are re-exported at the cranelisp_types crate root.
   use cranelisp_types::{CodeStore, LinkerStore};
   pub type SymbolTables<C = (), L = ()> =
       dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>;
   ```

   Then add `<C: CodeStore, L: LinkerStore>` to the fns that take `&SymbolTables`:
   `auto_schedule_defn`, `transform_expr`, `classify_expr`, `scheduling_class_from_table`
   (incl. its inner `walk`), `rebuild_chain`, `recurse_children`, and the live-but-
   `#[allow(dead_code)]` `scheduling_of` (genericize it too so the test module compiles
   uniformly; the `auto_schedule_expr*` helpers similarly). The body of each is
   **unchanged** — `table.get(name)` returns `&ModuleEntry<C>` and the two match arms
   above already ignore `C`. `apply_bind_chain_analysis` (`session_setup.rs:329`) then
   takes `&dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>` directly
   (or the generic `&SymbolTables<C, L>`), so `ctx.symbol_tables` passes with no
   `into_concrete` / view construction.

   **Fallback (only if genericization snags):** read `auto_schedule_defn` through a
   `&SymbolTable<(), ()>` *view* — but this needs a per-module re-projection of a
   `DashMap` and is strictly more code than the generic-param change; prefer the
   generic form. Either way **no `cranelisp-types` change** (`/arch` confirmed: both
   read fields exist at the `()/()` boundary and `SymbolTable<C, L>` is already
   maximally generic). If implementation somehow forces a `cranelisp-types` edit,
   STOP and file FIXME `target: /arch` — do not edit the types crate from int.

### 5.4 Cheap-skip guard (replaces the stale `scheduling_registry.is_empty()`)

The stale design guarded on `session.scheduling_registry.is_empty()`. That field no
longer exists (the registry was deleted in S57 Wave 3 G8 — scheduling class now lives
on `DefKind::PlatformEffect`, `bind_chain_analysis.rs:6–7`). The post-S78 cheap skip:
the pass walks `final_working` and, for each `bind!`-derived chain, looks up the
callee's class via the symbol tables; a module with **no** loaded platform DLL has no
`PlatformEffect` entries, so every `classify_expr` returns `Sequential` and no
`ParBind` is ever emitted — the pass is already a near-no-op for pure programs (one
AST walk, no allocation of `ParBind` nodes). The remaining cost is the single
recursive `transform_expr` walk per body. If profiling shows that walk is material
for pure Ring-0..3 programs (it should not be — it is one pass over already-built
ASTs), a cheap presence guard can be added: skip the call when the module's own table
+ its transitive imports contain zero `PlatformEffect` entries. **This guard is
optional and NOT part of the soundness contract** — recommend landing without it and
adding only if a measured regression appears. (Do NOT resurrect a syntactic
program-scan gate — the `program_uses_*` family was deleted in S66 Wave 3a-γ for the
reasons in FIXME 0178; gate on table contents, never on a source scan.)

### 5.5 Module Location (unchanged)

The pass lives in `src/bind_chain_analysis.rs` in the binary crate, since it requires
platform scheduling data (read from the session symbol tables) that is only available
at the pipeline integration level. It is not suitable for the backend crate (needs the
live tables) or the frontend crate (not a parsing concern). The `apply_bind_chain_analysis`
driver lives in `src/session_setup.rs`; the algorithm in `src/bind_chain_analysis.rs`.

### 5.6 Historical: the stale pre-S78 three-flow design (retained for context)

The original §5 specified three separate insertion points (`compile_single_module`,
`compile_and_run`, and a `ReplInput::Defn` REPL hook mirroring
`sketch/src/repl/input.rs:303`). All three entry points were retired by the S78
in-call-stack restructure, which collapsed the per-mode flows into the single
`process_cluster_once` core (`src/CLAUDE.md` §"Cluster-Atomic Orchestration",
S78 status). The single-seam design in §5.1 supersedes the three-flow design: one
seam, mode-uniform by construction, is strictly better than three hooks that must be
kept in sync (the three-hook shape was itself a mode-uniformity hazard of exactly the
kind Principle 11 — single pipeline, mode parameters — warns against).

---

## 5b. Transform-correctness contract (PO-0367.1) — case → enforcing-function map

The S84 architecture review (`sprints/SPRINT.md` §2, PO-0367.1) pins the Par-emission
contract as the cheapest soundness guard, checkable as **pure deterministic
AST-property assertions** (no concurrency in the test). Each MUST-emit / MUST-NOT-emit
case below maps to the grouping-logic function that enforces it, with a gap flag where
the live wiring could expose a weakness the unit tests must pin.

| # | Case | Required outcome | Enforcing function (`bind_chain_analysis.rs`) | Gap flag |
|---|---|---|---|---|
| C1 | Data-independent + different-resource-token (or token-0 / `Commutative`) pair | **MUST emit** `ParBind` (≥2 bindings) | `rebuild_chain` `:314` — `sc != Sequential && is_independent(...)` accumulates into `current_par`; `flush_par_group` `:283` emits `Parallel` when `len() >= 2` | — |
| C2 | Data-dependent binding (later binding refs an earlier-bound name) | **MUST NOT** Par-group (stays sequential) | `is_independent` `:247` over `free_vars_expr` `:252` — disjointness of the io_expr's free vars vs `all_bound` (committed + current group, `:309`) | **G1** (below) |
| C3 | Same non-zero resource token pair | **MUST NOT** be hoisted to independent branches (serial group at most, never independent) | — see **G2** | **G2** (below) |
| C4 | `Sequential`-class pair (e.g. `read-line`/`print` ordering) | **MUST NOT** Par-group | `rebuild_chain` `:314` — `sc != Sequential` is the gate; a `Sequential` callee fails it and is flushed as `Segment::Sequential` `:324` | — |
| C5 | Single eligible binding (1-element group) | demote to sequential bind (no `ParBind` overhead) | `flush_par_group` `:287` — `len()==1` arm demotes to `Segment::Sequential` | — |
| C6 | Non-platform-call io_expr (wrapper fn, nested bind, let) | conservatively `Sequential` | `classify_expr` `:179` — only `Apply(Var(name), ..)` resolving to a `PlatformEffect` entry is classified; everything else → `Sequential` `:202` | — |

### Negatives preservation — the green-on-arrival guard set (FIXME 0367, S85 item 4)

The wiring change-set MUST NOT regress the two AST-shape negatives the spec demands —
**a data-dependent binding** and **a `read-line`/`print` `Sequential`-class pair** MUST
NOT par-group. These are *already* enforced by the grouping logic (C2/C4 above) and
*already* guarded by EXISTING unit tests in `src/bind_chain_analysis.rs::tests`. The
wiring (genericizing the alias + adding the call site + dropping `#[allow(dead_code)]`)
touches the *plumbing*, not the grouping logic, so these tests must stay **green from the
first compile** — a red here means the genericization accidentally changed behaviour and
is a stop-the-line signal for `/dev`:

| Negative | Existing guard (`bind_chain_analysis.rs::tests`) | Asserts |
|---|---|---|
| C2 — data-dependent stays sequential | `test_dependent_commutative_stays_sequential` (`:751`) | a later io_expr referencing an earlier-bound name (the `Apply`-arg case) → result is NOT `ParBind` |
| C2 — independence predicate | `test_dependent_expression` (`:696`) | `is_independent` returns `false` when the bound name appears free |
| C4 — Sequential-class pair stays sequential | `test_sequential_stays_sequential` (`:731`) | two `print`s (`Sequential` class) → no `ParBind` |
| C4 — Sequential is the classification default | `test_classify_sequential_default` (`:663`) | a non-platform / `Sequential` callee classifies `Sequential` |
| C5 — single eligible binding demoted | `test_single_element_demoted` (`:771`) | a 1-element eligible group → no `ParBind` (sequential bind, no overhead) |
| C6 — non-platform call conservatively sequential | `test_classify_sequential_default` (`:663`) | wrapper/nested-bind/let io_exprs are not classified parallel |
| (positive control) C1 — independent pair groups | `test_two_commutative_independent_become_par_bind` (`:704`) | independent non-`Sequential` pair → one `ParBind` (2 bindings) |

The §8.1 ADD list (data-dependency negative over the remaining `Expr` variants;
idempotency; mixed-segmentation) extends these — but the seven above are the **regression
guards that exist today and must remain green** as the literal embodiment of S85 Scope
item 1's "Verify negatives still hold." These are unit tests in the `cranelisp` lib
target (`src/bind_chain_analysis.rs::tests`); after genericizing the `SymbolTables` alias,
`cargo nextest run -p cranelisp -E 'test(bind_chain)'` is the fastest confirmation the
plumbing change preserved the grouping contract before running the full suite.

### Gap G1 — `free_vars_expr` correctness is the C2 soundness load-bearer

C2 (the data-dependency negative) reduces entirely to `free_vars_expr` (`cranelisp-types`)
computing the *complete* free-variable set of an `io_expr`. If `free_vars_expr` under-reports
a free var (misses a capture in some `Expr` variant), a dependent binding would be wrongly
classified independent and hoisted into a `ParBind` — a **soundness violation** (reordering
a data-dependent effect). This is not int-owned code (it is `cranelisp-types`), but the
*reliance* is int's. **The §8.1 unit tests MUST include the dependency negative over every
`Expr` variant that can carry a free var** (`Apply` arg, `Let` binding RHS, `If` branches,
`Match` scrutinee+arms, `Lambda` body minus its own params, `VecLit`, `Annotate`, `ConstrADT`
field, nested `ParBind`). If a variant is found under-reported, file FIXME `target: /arch`
(the type lives in `cranelisp-types`, `/arch`-owned) — NOT a local int patch. The current
tests cover only the `Apply`-arg case (`test_dependent_expression` `:696`); the gap is the
remaining variants.

### Gap G2 — same-non-zero-token serial grouping is NOT enforced at the int seam (it is the trampoline's job)

This is the most important gap to record correctly, because it determines what the int-seam
unit tests can and cannot prove. **The bind-chain analysis pass does NOT distinguish "same
non-zero token" from "different token" — it groups by `SchedulingClass` (`Sequential` vs
non-`Sequential`) and data-independence ONLY** (`rebuild_chain` `:314`). Two
`ResourceSerial` calls with the **same** token that are data-independent WILL be grouped
into one `ParBind` by this pass. C3's "MUST NOT be hoisted to independent branches" is
**not** enforced here — it is enforced **at runtime by the trampoline's token grouping**:
`dispatch_par_branches` groups branches by resource token into
`WorkItem::SerialGroup` (same non-zero token → run sequentially) vs `WorkItem::Single`
(token-0 / independent → run concurrently) (per FIXME 0367 / `design/backend/io-scheduling.md`
§5.2). So a `ParBind` over two same-token `ResourceSerial` calls is *correct*: the compile
pass emits the `ParBind`, and the trampoline serialises the same-token branches **inside** it.

**Implication for the contract.** C3 at the *AST seam* is therefore satisfied vacuously —
the pass never produces "independent branches" as a runtime concept; it produces a `ParBind`,
and "independent vs serial" is a runtime token decision. The int-seam unit tests (§8.1)
assert the AST-property facts they CAN: C1 (independent diff-class → `ParBind`), C2
(data-dependent → no `ParBind`), C4 (Sequential → no `ParBind`), C5/C6. The same-token
serialisation guarantee (C3 proper) is witnessed by the **runtime timing pair** in PO-0367.3
(`resource_serial_same_token_serializes` staying green), NOT by an int-seam unit test. This
is the correct division: the int pass is a single-threaded AST transform whose contract is
"emit `ParBind` for independent non-Sequential pairs"; the token-serialisation contract lives
in the already-tested trampoline dispatch (which 0367 does NOT modify — `sprints/SPRINT.md`
§2 point (b)). **No gap in the wiring** — but the test plan must place each guard at the
layer that can actually witness it (§8). Record: do NOT attempt to assert same-token
serialisation at the int unit-test seam; it is structurally not observable there.

### Disjointness from the scheduler surface (confirming the /arch read)

Source-read confirmation of `sprints/SPRINT.md` §2 point (a)/(b): the wired pass
(`auto_schedule_defn` → `transform_expr`) takes `&mut Defn` + `&SymbolTables` (read-only)
+ `&ModuleFullPath`, spawns no threads, takes no locks, and touches no scheduler state — it
runs inside `finalize_cluster`, the worker's own sequential per-cluster phase. The only shared
structure it reads is `ctx.symbol_tables` (a `DashMap`, already thread-safe, read during this
worker's own phase). **No contradiction with the /arch read was found** — the Par *dispatch*
path (`dispatch_par_branches`) is not touched by this wiring and shares no state with the
scheduler. (If `/dev`(int) finds otherwise during implementation, that is a FIXME `target: /arch`
+ Phase-5 escalation per the review, not a Phase-3 design change.)

## 5c. Flag-staging the live activation (S84 — RECOMMENDED, non-mandatory)

Per the /arch review (`sprints/SPRINT.md` §2, "Staging behind a flag — RECOMMENDED"),
the wiring flips a previously-inert feature ON across all three modes at once. The
review *recommends* (does not mandate) an env-gated activation defaulting **ON**, so
that (a) if an unforeseen interaction surfaces the pass can be disabled at the seam
without reverting the change-set, and (b) the PO-0367.1 negatives can be checked with
the pass forced on.

### Flag design

| Property | Value |
|---|---|
| Flag name | `CRANELISP_NO_IO_SCHEDULE` |
| Semantics | **Presence disables** the pass (default = absent = pass ON). Matches the existing src/ convention: boolean flags are presence-checked via `std::env::var("CRANELISP_*").is_ok()` (see `CRANELISP_CODEGEN_TRACE`, `CRANELISP_IO_TRACE`). |
| Default | **ON** (pass runs). The feature is a §10.12 MUST — default-on is correct; the flag is an escape hatch, not an opt-in. |
| Check location | **Once**, at the call site in `finalize_cluster` (`src/process_form.rs`, §5.3 step 2) — NOT per-defn. Reading the env var once per cluster is cheap; reading per-body is wasteful. |

```rust
// In finalize_cluster, between :1058 and :1060 (the §5.3 seam):
if std::env::var("CRANELISP_NO_IO_SCHEDULE").is_err() {
    crate::session_setup::apply_bind_chain_analysis(
        &mut final_working, ctx.symbol_tables, module,
    );
}
```

### Naming rationale

- `CRANELISP_NO_IO_SCHEDULE` (not `CRANELISP_NO_PARALLEL`) keeps IO scheduling
  (§10.12) **separate** from lenient eval (§12.4.3) — the two are independent features
  with different safety profiles (§6). A debugger isolating an IO-ordering anomaly
  disables *this* pass without also disabling pure-let parallelism, and vice versa.
- The `NO_`-prefix presence-disables convention means the common path (no env var)
  gets the pass — no env read changes the default-on behaviour.

### Optionality (per /arch)

The flag is a **convenience, not a soundness precondition** — the blast radius is one
compile-time pass + one already-tested runtime dispatch path, not the scheduler. **If a
clean unconditional wiring lands with PO-0367.1–.3 all green, the flag is optional and
MAY be dropped.** Recommend landing WITH the flag for the first cut (it costs one
`env::var` check and bounds the blast radius during the sprint), then a follow-up may
remove it once the timing witnesses are stably green. The PO-0367.1 unit tests call
`apply_bind_chain_analysis` (or `auto_schedule_defn`) **directly**, bypassing the env
gate — so the negatives are always checked with the pass forced on regardless of the
flag state (the flag gates only the pipeline call site, not the function).

## 6. CRANELISP_NO_LENIENT Interaction

`CRANELISP_NO_LENIENT` is specified in the sprint plan to disable lenient evaluation — the automatic parallelisation of pure `let` bindings (spec §12.4.3).

Automatic IO scheduling (spec §10.12) is a **different feature**: it parallelises effectful `bind!` chains, not pure `let` bindings. The two features share a thread pool but are otherwise independent in semantics, analysis, and codegen.

### Recommendation: Separate Concerns

`CRANELISP_NO_LENIENT` should **only** affect pure let parallelism (lenient evaluation). It should **not** disable IO scheduling. Rationale:

1. **Spec separation**: §12.4.3 (lenient eval) and §10.12 (IO scheduling) are separate spec sections with independent semantics.
2. **Debugging needs differ**: A user debugging IO ordering issues needs to disable IO parallelism specifically. A user debugging a performance regression in pure code needs to disable lenient eval specifically.
3. **Safety profiles differ**: Lenient eval is semantically transparent for pure expressions. IO scheduling is semantically transparent only for Commutative effects. The correctness arguments are different.

The IO-scheduling kill switch is `CRANELISP_NO_IO_SCHEDULE` — its full design (name,
default-on semantics, single check at the `finalize_cluster` seam) is specified in
**§5c**. The stale code snippet that previously lived here (guarding on the deleted
`session.scheduling_registry` field and the retired `compile_single_module` flow) is
removed; see §5c for the live snippet against the post-S78 seam.

### Alternative: Single Kill Switch

If a single env var is preferred for simplicity, `CRANELISP_NO_PARALLEL=1` could disable both features. This is simpler but less precise for debugging. Not recommended as the default, but acceptable if the user prefers it.

---

## 7. Sketch Comparison

### What `schedule.rs` Does

The sketch's `schedule.rs` (367 lines) implements the full bind chain analysis:

| Component | Sketch | Lines |
|---|---|---|
| `auto_schedule_defn()` | Public entry: swaps body, transforms, replaces | 31-34 |
| `transform_expr()` | Recursive dispatcher: detect bind chain or recurse children | 39-47 |
| `is_bind_chain_start()` | Pattern match for `Apply(Var("bind"), [_, Lambda([_], _)])` | 50-55 |
| `is_bind_var()` | Check callee is "bind" or "*/bind" | 58-63 |
| `collect_bind_chain()` | Flatten nested binds into `Vec<(name, expr, annotation, span)>` | 69-102 |
| `classify_expr()` | Look up scheduling class via `tc.scheduling_of()` | 108-123 |
| `is_independent()` | Free variable disjointness check | 126-132 |
| `Segment` enum | Sequential / Parallel grouping | 137-142 |
| `flush_par_group()` | Flush parallel group: ≥2 → Parallel, 1 → demote, 0 → noop | 149-168 |
| `rebuild_chain()` | Group chain, fold right-to-left into ParBind / bind calls | 171-232 |
| `make_bind()` | Reconstruct a sequential bind `Apply` expression | 235-258 |
| `recurse_children()` | Recursively transform sub-expressions for non-bind nodes | 265-366 |

The sketch preserves `Lambda` parameter type annotations through the chain collection (the `annotation` field in the tuple), which is important for round-tripping — annotations set by the user or by the macro expander must not be lost during AST rewriting.

### Reimplementation Follows

The reimplementation follows the sketch's algorithm closely. The core logic — chain collection, classification, grouping, reconstruction — is the same. This is justified because:

1. The algorithm is dictated by the spec (§10.12.1): pairwise data independence + scheduling class check.
2. The sketch's approach is clean, well-structured, and handles edge cases correctly (single-element groups, nested chains, annotation preservation).
3. There is no architectural reason to diverge.

### Reimplementation Diverges

| Aspect | Sketch | Reimplementation | Rationale |
|---|---|---|---|
| Scheduling data source | `tc.scheduling_of()` on TypeChecker | `scheduling_of()` on a separate `HashMap<Symbol, SchedulingClass>` | Keep typechecker free of platform dependencies |
| Free variable function | `crate::captures::free_vars()` in same crate | `cranelisp_types::free_vars_expr()` or local implementation | Pass lives in binary crate, needs AST free-var analysis |
| Module location | `src/schedule.rs` alongside other compiler modules | `src/bind_chain_analysis.rs` in binary crate | Pass needs pipeline-level data (scheduling registry) |
| Env var control | None (always runs) | `CRANELISP_NO_IO_SCHEDULE` env var to disable | Debugging aid not present in sketch |
| Body swap technique | `std::mem::replace` with dummy `BoolLit` | Same approach | Avoids cloning the entire body |

The body-swap technique (`std::mem::replace` with a dummy expression) is necessary because `auto_schedule_defn` takes `&mut Defn` — it needs to extract the body, transform it, and put it back. The dummy `BoolLit` is never observed (replaced before the function returns).

---

## 8. Testing Strategy (S84 — mapped to PO-0367.1/.2/.3)

The proof obligation has three parts, each placed at the layer that can witness it
(§5b Gap G2 is the load-bearing reason the layers differ). `/dev`(int) owns §8.1
(unit, alongside the wiring); `/qa` owns §8.2–§8.3 (e2e).

### 8.1 PO-0367.1 — int-seam unit tests (deterministic AST-property assertions; `/dev` on int)

These are pure AST-property assertions — **fully deterministic, no concurrency in the
test** — that call `auto_schedule_defn` / `transform_expr` directly (bypassing the env
gate, §5c). Several already exist in `src/bind_chain_analysis.rs::tests`; the S84
additions pin the negatives the contract requires (§5b). The seam is the test module
in `src/bind_chain_analysis.rs`:

**MUST-emit positives:**
- C1 — `test_two_commutative_independent_become_par_bind` (`:704`, EXISTS) — independent
  non-`Sequential` pair → one `ParBind` with 2 bindings.

**MUST-NOT-emit negatives (the cheapest soundness guard — these are the S84 additions):**
- C2 — data-dependent binding stays sequential. `test_dependent_commutative_stays_sequential`
  (`:751`, EXISTS) covers the `Apply`-arg case. **ADD** the dependency-negative over the
  remaining `Expr` variants that can carry a free var (Gap G1): `Let`-RHS, `If`-branch,
  `Match`-scrutinee/arm, `Lambda`-body, `VecLit`-elem, `Annotate`, `ConstrADT`-field,
  nested `ParBind`. Each asserts: a later io_expr referencing an earlier bound name via
  that variant → result is NOT `ParBind`.
- C4 — `test_sequential_stays_sequential` (`:731`, EXISTS) — `Sequential`-class pair
  (two `print`s) → no `ParBind`.
- C5 — `test_single_element_demoted` (`:771`, EXISTS) — 1-element group → no `ParBind`.
- C6 — `test_classify_sequential_default` (`:663`, EXISTS) — non-platform call → `Sequential`.

**Idempotency (the retry-from-top requirement, §5.2):**
- **ADD** `test_transform_idempotent` — `transform_expr(transform_expr(e)) == transform_expr(e)`
  for an independent-pair chain (the result already contains a `ParBind`; re-running must
  not change it). This pins the §5.2 hard correctness requirement that `finalize_cluster`
  may run the pass multiple times on retries.

**Mixed segmentation:**
- **ADD** `test_mixed_chain_segments` — a `[independent, independent, dependent, independent]`
  chain produces `ParBind(2) → Sequential → Sequential` (the dependent step flushes the
  group, then stands alone). Pins `flush_par_group` boundary behaviour at the seam.

**Single-step launch E2 hardening (FIXME 0478 — the §3.7 fix; the shape the FIXME names):**
- **ADD** `test_launch_arm_refuses_same_token_continuation` — a chain whose discarded
  `ResourceSerial` middle step `(_ (send-conn conn r1))` is followed by a continuation that
  performs a **same-handle** effect `(send-conn conn r2)` MUST **NOT** lower to
  `Expr::LaunchContinue` (E2 fails — `io_expr` and `continuation` share the free var `conn`);
  it stays an ordinary `Bind`. This pins the 0478 hardening: without E2 the single-step arm
  wrongly detaches it, reordering two same-token effects. `// spec: 10-io.md §10.12.7 (E2
  value-locality)`.
- **ADD** `test_launch_arm_refuses_commutative_single_step` — a discarded `Commutative`
  (token-0) single step (e.g. a shared-`stdout` `print` with its result unused) MUST NOT
  launch (E3 — refuse shared-singleton token-0); only `ResourceSerial` single steps are
  launch-eligible. (The legitimate accept-loop launch — `conn` bound inside the launched
  sub-tree, absent from the continuation — stays GREEN: `test`-guard that the existing
  `concurrency_fanout` / accept-loop launch shape still emits `LaunchContinue`, so the
  hardening does **not** weaken the §B4 single-step launch the synthetic test guards.)

All §8.1 tests carry `// spec: 10-io.md §10.12.1` annotations. They are the Wave-0
failing-first guards the /arch refinement calls for ("the negatives are the cheapest
soundness guard and must exist before wiring") — authored before the §5.3 call site
lands.

### 8.2 PO-0367.2 — mode-uniformity e2e (`/qa`)

A guard showing the **same source emits the same Par-grouping decision in all three
modes** (`--run`, `--link`, REPL eval) — there must be NO mode that silently skips the
pass. Because §5.1 establishes the wiring is at the single shared `process_cluster_once`
core, this is structurally guaranteed; the e2e is the *witness* that the structural
property holds end-to-end. Candidate instrument: a program with one independent
`Commutative`/`ResourceSerial`-pair `bind!` chain, run under all three modes, asserting
identical observable scheduling (the timing witness of §8.3 under `--run` + `--link`,
plus a REPL-eval path that reaches the same `finalize_cluster` seam). `/qa` owns the
exact harness shape; the design point of record is **the seam is mode-uniform by
construction (single core)** — the e2e confirms it, it does not have to engineer it.

### 8.3 PO-0367.3 — the structured-fork-join timing witness (`/qa` + `/platform`)

The only genuinely-concurrent obligation, and it is narrow (§5b Gap G2; `sprints/SPRINT.md`
§2 PO-0367.3). The witness is the existing failing-not-ignored guard pair in
`tests/spec_10_io.rs`:

- `resource_serial_diff_token_parallelizes` — currently **RED** (diff-token wall-clock
  ~2× single-call because no `ParBind` is emitted). **Flips GREEN** when this wiring
  lands (diff-token concurrent wall-clock < 1.5× single-call duration, `--run` + `--link`).
  This is FIXME 0353's closure condition.
- `resource_serial_same_token_serializes` — currently GREEN; **MUST stay GREEN**. The
  regression guard that same-token branches still serialise (witnesses C3 proper, §5b
  Gap G2 — the trampoline's token-serialisation decision, which this wiring does NOT
  perturb).

The diff-token-parallelises + same-token-serialises pair together witness the
token-serialisation decision AND the fork-join join semantics — a sound proof for this
structured-fork-join surface (the S62 "timing/stress insufficient" caveat applies to the
*unstructured scheduler* surface, not this one; `sprints/SPRINT.md` §2).

### 8.4 Coverage of the older integration-test list

The pre-S84 integration list (commutative pairs → `ParBind`; sequential stays sequential;
mixed-chain segmentation; dependent-pair sequential; nested-in-lambda; flag disables;
zero-overhead skip) is **subsumed**: the AST-property facts are now §8.1 unit tests (the
right layer — deterministic, no e2e needed for AST shape); the runtime-observable facts
are §8.2–§8.3. The flag-disables case is a §8.1 call-site test (set `CRANELISP_NO_IO_SCHEDULE`,
assert the pipeline produces no `ParBind`) — but note the unit tests of the *function*
bypass the flag by design (§5c). Nested-in-lambda is a §8.1 case (`recurse_children`
descends into `Lambda` bodies, `bind_chain_analysis.rs:423`).
