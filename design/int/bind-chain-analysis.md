# Bind Chain Independence Analysis

Post-expansion, pre-typecheck pass that transforms `bind!`-expanded AST trees into `Expr::ParBind` nodes for automatic IO scheduling.

## References

- `spec/10-io.md` §10.12 — Automatic IO Scheduling
- `sprints/SPRINT.md` — Sprint 25 plan (/int task)
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

## 5. Pipeline Insertion Point

The pass runs **after AST building** and **before typechecking**, transforming `Defn` bodies in-place.

### Batch Mode (`compile_single_module`)

In `src/pipeline.rs`, `compile_single_module()` currently has this flow:

```
Phase 3: process_forms_sequentially (macro expansion)
Phase 4: build_program (AST building)           ← program: Vec<TopLevel>
Phase 5: tc.check_program(&program)              ← typechecking
Phase 6: compile_program                          ← codegen
```

Insert bind chain analysis between Phase 4 and Phase 5:

```rust
// Phase 4: Build program AST from accumulated sexps.
let mut program = cranelisp_frontend::build_program(
    &accumulated,
    &mut session.expander,
)?;

// Phase 4b: Bind chain independence analysis (auto IO scheduling).
// Transform eligible bind chains into ParBind nodes.
if !session.scheduling_registry.is_empty() {
    for item in &mut program {
        if let TopLevel::Defn(defn) = item {
            bind_chain_analysis::auto_schedule_defn(defn, &session.scheduling_registry);
        }
    }
}

// Phase 5: Typecheck
let check = session.tc.check_program(&program)?;
```

The `session.scheduling_registry.is_empty()` guard skips the pass entirely when no platform DLLs are loaded (the common case for pure programs, Ring 0-3 tests, etc.). This ensures zero overhead for programs that don't use IO.

### Simple Batch Mode (`compile_and_run`)

The same insertion applies to `compile_and_run()`:

```rust
let mut program = session.process_and_build_program(sexps)?;

// Bind chain analysis (auto IO scheduling).
if !session.scheduling_registry.is_empty() {
    for item in &mut program {
        if let TopLevel::Defn(defn) = item {
            bind_chain_analysis::auto_schedule_defn(defn, &session.scheduling_registry);
        }
    }
}

let check = session.tc.check_program(&program)?;
```

### REPL Mode

In the REPL eval path, individual forms are processed one at a time. When a `defn` is evaluated:

```rust
// After AST building, before typechecking:
if let ReplInput::Defn(ref mut defn) = input {
    if !self.scheduling_registry.is_empty() {
        bind_chain_analysis::auto_schedule_defn(defn, &self.scheduling_registry);
    }
}
```

This mirrors the sketch's approach at `sketch/src/repl/input.rs:303`.

### Module Location

The pass lives in a new module `src/bind_chain_analysis.rs` in the binary crate, since it requires platform scheduling data that is only available at the pipeline integration level. It is not suitable for the backend crate (needs platform data) or the frontend crate (not a parsing concern).

---

## 6. CRANELISP_NO_LENIENT Interaction

`CRANELISP_NO_LENIENT` is specified in the sprint plan to disable lenient evaluation — the automatic parallelisation of pure `let` bindings (spec §12.4.3).

Automatic IO scheduling (spec §10.12) is a **different feature**: it parallelises effectful `bind!` chains, not pure `let` bindings. The two features share a thread pool but are otherwise independent in semantics, analysis, and codegen.

### Recommendation: Separate Concerns

`CRANELISP_NO_LENIENT` should **only** affect pure let parallelism (lenient evaluation). It should **not** disable IO scheduling. Rationale:

1. **Spec separation**: §12.4.3 (lenient eval) and §10.12 (IO scheduling) are separate spec sections with independent semantics.
2. **Debugging needs differ**: A user debugging IO ordering issues needs to disable IO parallelism specifically. A user debugging a performance regression in pure code needs to disable lenient eval specifically.
3. **Safety profiles differ**: Lenient eval is semantically transparent for pure expressions. IO scheduling is semantically transparent only for Commutative effects. The correctness arguments are different.

If a separate env var is desired for IO scheduling, use `CRANELISP_NO_IO_SCHEDULE=1`. Implementation:

```rust
// In the pipeline, before calling auto_schedule_defn:
let io_schedule_enabled = std::env::var("CRANELISP_NO_IO_SCHEDULE").is_err();

if io_schedule_enabled && !session.scheduling_registry.is_empty() {
    for item in &mut program {
        if let TopLevel::Defn(defn) = item {
            bind_chain_analysis::auto_schedule_defn(defn, &session.scheduling_registry);
        }
    }
}
```

The env var check is done once at the pipeline entry point, not per-defn.

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

## 8. Testing Strategy

### Unit Tests (in `src/bind_chain_analysis.rs`)

- **Pattern recognition**: `is_bind_chain_start` correctly identifies bind patterns and rejects non-bind forms.
- **Chain collection**: `collect_bind_chain` flattens 1, 2, 3+ deep chains correctly.
- **Classification**: `scheduling_of` returns correct class for bare names, qualified names, and unknown names.
- **Independence**: `is_independent` correctly detects free variable overlap.
- **Grouping**: 2 commutative independent → 1 ParBind; 2 sequential → 2 sequential binds; mixed chains group correctly; single-element groups demote.

### Integration Tests (owned by `/qa`)

- Commutative + data-independent bind pairs produce `ParBind` AST nodes.
- Sequential bind pairs remain as sequential bind calls.
- Mixed chains: commutative pair followed by sequential step correctly segments.
- Dependent commutative pair (one uses other's binding) stays sequential.
- Nested bind chains inside lambdas are also transformed.
- `CRANELISP_NO_IO_SCHEDULE=1` disables the pass entirely.
- Programs without platform declarations skip the pass (zero overhead).
