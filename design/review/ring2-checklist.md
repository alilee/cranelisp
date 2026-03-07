# Ring 2 Review Checklist

Ring 2 specific review criteria. Apply AFTER the general `checklist.md`. Ring 2 property: **Traits, modules, imports/exports, constrained polymorphism, monomorphisation, multi-signature dispatch, auto-curry. Name resolution and dispatch established.**

Ring 2 exercises: `cranelisp-typecheck` (trait declarations, implementations, method resolution, constrained polymorphism, monomorphisation, module-scoped type environments), `cranelisp-backend` (mangled name dispatch, GOT-based cross-module calls, trait method -> primitive mapping), `cranelisp-frontend` (trait/impl syntax, import/export/mod declarations, module file extraction), `cranelisp` binary crate (module graph pipeline, REPL trait/module extensions), and `cranelisp-types` (boundary types for traits, modules, constrained poly).

---

## 1. Trait System Correctness (Mandatory)

Derived from `spec/07-traits.md` and arch decisions 14-19. The trait system is Ring 2's primary addition and the most complex subsystem. Incorrect trait dispatch would corrupt every operator expression.

- [ ] **Trait declarations register method signatures.** `(deftrait (Num a) (+ [a a] a) ...)` registers each method with its type signature. Method names map to their owning trait via `method_to_trait`.
- [ ] **Trait implementations type-check method bodies.** `(impl Num Int (defn + [x y] (add-i64 x y)))` verifies that the body type matches the trait method's type signature, with `SelfType` resolved to the impl target type.
- [ ] **Default methods synthesize bodies when not overridden.** `Eq.!=` generates `(not (= x y))`. `Ord.>`, `Ord.<=`, `Ord.>=` generate correct comparisons. The default body AST is built correctly.
- [ ] **Method resolution produces `ResolvedCall::TraitMethod`.** Operators like `+` resolve to `TraitMethod { trait_name, method_name, impl_type }` after concrete type determination. The typecheck crate never emits inline IR -- only resolution data.
- [ ] **Backend maps `TraitMethod` to primitives via `primitive_for_trait_method`.** Known primitive impls (Num.+$Int -> add-i64) short-circuit to inline IR. Unknown impls (user-defined) dispatch to compiled function calls. Per arch decision 14.
- [ ] **Ring 0 `BuiltinFn` path coexists with Ring 2 `TraitMethod`.** Named primitives (`add-i64`, etc.) retain their existing resolution. Operators (`+`, `<`, etc.) gain the `TraitMethod` path. Both coexist per arch principle 9 (rings are accretive).
- [ ] **JIT mangling follows convention.** Trait method impls: `Trait.method$Type` (e.g., `Num.+$Int`). Constrained fn specializations: `name$Type1+Type2`. Per arch decision 16.
- [ ] **Constraint propagation works in `generalize`.** When a function body uses `+`, the type variable gains a `Num` constraint. `Scheme.constraints` is populated by checking active constraints on quantified variables, resolved through the substitution.
- [ ] **Deferred trait call resolution handles both passes.** During Pass 2 body checking, some trait method calls have unresolved args. `resolve_deferred_trait_calls` runs after each body and again after all bodies are generalized (Phase 3), catching calls whose types were pinned by later code.

## 2. Constrained Polymorphism and Monomorphisation (Mandatory)

Derived from `spec/07-traits.md` and arch decision 19. Constrained polymorphism is the mechanism that bridges generic code with concrete dispatch.

- [ ] **Constrained functions are detected after generalization.** `(defn add [x y] (+ x y))` is detected as constrained (`Num` constraint on its type vars). Eager detection in Pass 2 runs before later call sites could pin type vars.
- [ ] **Monomorphisation generates concrete specializations.** `(add 1 2)` triggers `monomorphise_call`, producing `add$Int+Int` with concrete param types and its own `method_resolutions` and `expr_types`.
- [ ] **Per-specialization method resolutions are isolated.** Each `MonoDefn` carries its own `resolutions` HashMap. The main typechecker's resolutions are saved and restored around body re-checking. No cross-contamination.
- [ ] **Constraint verification checks impl existence.** Before generating a specialization, `monomorphise_call` verifies that required trait impls exist for the concrete types. Missing impls produce a clear error.
- [ ] **Call sites receive `SigDispatch` resolution.** Each concrete call to a constrained fn is recorded in `method_resolutions` with `ResolvedCall::SigDispatch { mangled_name }` so the backend can emit the direct call.
- [ ] **Batch and REPL monomorphisation paths produce identical results.** `pass4_monomorphise` (batch) and `monomorphise_expr_calls` (REPL) both call `monomorphise_call`. The REPL path also compiles mono defns before expression evaluation.
- [ ] **Self-recursive constrained calls in mono bodies are handled.** `monomorphise_call` scans the mono body for inner constrained-fn calls and adds `SigDispatch` entries for them.

## 3. Module System Correctness (Mandatory)

Derived from `spec/08-modules.md`. The module system introduces cross-file compilation, visibility, and import resolution.

- [ ] **Module graph discovery resolves files per spec section 8.2.5.** Search order: child directory, sibling file, project root, lib directory. Each search candidate is tried in order.
- [ ] **Cycle detection prevents infinite recursion.** `discover_module_recursive` maintains a `visiting` stack. Re-entry into a module on the stack produces a clear error with the cycle path.
- [ ] **Topological sort compiles dependencies before dependents.** Kahn's algorithm processes zero-in-degree modules first. The entry module is compiled last.
- [ ] **Imports register symbols in the current module's table.** `register_imports` processes `Glob`, `Specific`, and aliased imports. Imported symbols create `ModuleEntry::Import { source }` entries pointing to the source module.
- [ ] **Visibility is enforced.** Private definitions (`defn-`) are not importable. Glob imports skip private symbols. Qualified access to private names from outside the subtree produces a type error.
- [ ] **Ambiguity detection for conflicting imports.** Same bare name from different sources produces `ModuleEntry::Ambiguous` per spec section 8.6.4.
- [ ] **Module aliases work.** `(import [core.option :as opt])` registers an alias so `opt/Some` resolves correctly.
- [ ] **Qualified name resolution follows spec section 8.6.6.** `module/name` tries child-of-current-module first (submodule reference), then absolute path.
- [ ] **Builtin seeding for new modules.** When switching to a new module, builtins (primitives, special forms, constructors, type defs) are copied as Import entries from the "user" module. This ensures primitives work in all modules.

## 4. Multi-Sig Dispatch and Auto-Curry (Mandatory)

Derived from `spec/05-definitions.md` and `spec/04-expressions.md`.

- [ ] **Multi-sig functions dispatch on arity.** `(defn f ([x] ...) ([x y] ...))` resolves the correct variant based on argument count.
- [ ] **Multi-sig functions dispatch on type.** `(defn show ([Int x] ...) ([Bool x] ...))` resolves by matching concrete arg types.
- [ ] **Auto-curry returns a closure.** Calling a function with fewer args than its arity returns a closure that captures the partial arguments.
- [ ] **Resolution order is correct.** Constrained fn detection -> method resolution -> multi-sig name building -> monomorphise -> overload resolution -> method resolution (unified pipeline).

## 5. Cross-Module GOT and Codegen (Mandatory)

Derived from `design/arch/interfaces.md` and the Ring 2 backend deliverables.

- [ ] **GOT-based function calls in interactive mode.** Functions call through `GOT[slot]` so redefinition updates all call sites.
- [ ] **GOT slot management is correct.** `ensure_slot_for` reuses existing slots. `allocate_slot` returns an error when the GOT is full.
- [ ] **Cross-module function calls resolve via shared JIT.** In `compile_module_graph`, all modules compile into a single JIT. Dependencies' function signatures are accumulated for downstream module declarations.
- [ ] **Module qualified aliases are registered.** Submodule functions get qualified aliases (e.g., `util/helper`) for cross-module reference.
- [ ] **JIT lifetime management.** In REPL mode, each compilation creates a new JIT that is kept alive in `jit_modules` so code pointers remain valid.

## 6. Ring 0-1 Regression (Mandatory)

- [ ] **All Ring 0 tests pass unchanged.** The 105 Ring 0 tests in `tests/ring0.rs` must pass with zero modifications.
- [ ] **All Ring 1 tests pass unchanged.** The 162 Ring 1 tests in `tests/ring1.rs` must pass with zero modifications.
- [ ] **All RC tests pass (excluding known ignored).** The 74 passing RC tests in `tests/rc.rs` must continue to pass.
- [ ] **All REPL experience tests pass.** The 178 REPL experience tests must continue to pass.
- [ ] **All examples pass.** The 15 example tests must continue to pass.
- [ ] **Rings are accretive.** No prior-ring test was deleted or modified to accommodate Ring 2 changes.

## 7. RC Correctness for Ring 2 Types (Important)

Derived from Ring 1 checklist section 2 and the Ring 2 additions (trait method dispatch, closures returned from trait methods, ADT fields through function boundaries).

- [ ] **Trait method dispatch does not leak.** When `(+ s1 s2)` resolves to `str-concat` for Strings, the consuming/borrowed convention is correct.
- [ ] **Monomorphised function boundaries handle heap types.** Specializations like `add$String+String` must emit correct RC for heap-typed parameters.
- [ ] **Known RC bugs are documented with ignored tests.** The 3 known RC bugs have `#[ignore]` tests with clear messages explaining the root cause.

## 8. Code Quality (Mandatory)

Ring 2 introduces the most code of any ring (~6000 new lines). Quality standards must hold.

- [ ] **No `unwrap()` in pipeline code.** Only in tests and `main()`.
- [ ] **No `panic!()` in pipeline code.** Only `unreachable!("invariant: ...")` for true programmer errors.
- [ ] **No function exceeds 100 lines.** Decompose into named helpers.
- [ ] **Clippy clean.** Zero warnings across all crates.
- [ ] **Max 8 parameters per function.** Group related parameters into context structs.

## 9. Design Documentation (Important)

- [ ] **Trait system design doc exists.** Describes declaration, implementation, method resolution, default methods, constraint propagation.
- [ ] **Module system design doc exists.** Describes discovery, toposort, import processing, visibility, cross-module codegen.
- [ ] **Constrained polymorphism design doc exists.** Describes detection, monomorphisation, per-specialization isolation.
- [ ] **Cross-module codegen design doc exists.** Describes GOT, shared JIT, function signature accumulation.

## 10. Code Structure (Mandatory)

- [ ] **No god objects.** `TypeChecker` is large but decomposed via `impl` blocks in separate modules. No single struct accumulates unrelated responsibilities.
- [ ] **Clear crate boundaries maintained.** Backend does not depend on typecheck. Frontend does not depend on backend. `cranelisp-types` remains data-only.
- [ ] **Named structs for multi-field returns.** `MonoDefn`, `RegisteredImpl`, `TraitRegistry`, etc.

---

## Ring 2 Acceptance Gate

Before Ring 2 is declared complete, `/review` verifies:

1. **All items on this checklist pass.** Every checkbox is checked or has an explicit waiver with rationale.
2. **All items on `checklist.md` (general) pass.**
3. **Zero Blocker findings outstanding.** Any Blocker finding must be resolved before the gate.
4. **Important findings acknowledged.** Each Important finding is either resolved or explicitly deferred with rationale.
5. **Ring 2 roadmap acceptance criteria pass.** Per `design/arch/roadmap.md`:
   - Trait declarations and implementations type-check
   - Constrained polymorphic functions monomorphise at call sites
   - Cross-module imports work
   - Multi-sig dispatch works
   - Auto-curry works
   - ~150 additional integration tests green
6. **Ring 0-1 regression gate passes.** All prior-ring tests pass unchanged.
7. **`cargo clippy` status documented.** Clean or all warnings acknowledged.
8. **Design docs current.** Each compiler skill that added Ring 2 code has design documentation.

## Cross-References

- `design/review/checklist.md` -- general checklist (apply first)
- `design/review/ring1-checklist.md` -- Ring 1 checklist (Ring 0-1 items carry forward)
- `design/review/ring1-report.md` -- Ring 1 completion report (deferred items carry forward)
- `design/arch/roadmap.md` -- Ring 2 acceptance criteria
- `design/arch/CLAUDE.md` -- architectural decisions 14-19
- `spec/07-traits.md` -- trait specification
- `spec/08-modules.md` -- module specification
- `tests/plan/ring2.md` -- Ring 2 test plan
- `tests/plan/strategy.md` -- test strategy and ring gate criteria
