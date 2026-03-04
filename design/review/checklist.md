# General Review Checklist

Review checklist applicable to ALL rings. Derived from `src/CLAUDE.md` conventions, `design/arch/CLAUDE.md` architectural principles, and common patterns across all four prototype audit files.

Use this checklist alongside the ring-specific checklist for the ring under review.

---

## 1. Error Handling

These items derive from `src/CLAUDE.md` "Error Handling" and typechecker audit HIGH-4, HIGH-5, codegen audit MED-1.

- [ ] **No `unwrap()` in pipeline code.** `unwrap()` is permitted only in `#[test]` functions and in `main()`. Use `?` with `CranelispError` for fallible operations.
- [ ] **No `expect()` in pipeline code.** If the value might be `None`/`Err` due to user input, return a proper `CranelispError` with a span. If it is a programmer invariant, use `unreachable!("invariant: <description>")`.
- [ ] **No `panic!()` on user input.** `unreachable!("invariant: <description>")` is acceptable only for true programmer errors -- logic bugs that should never occur given correct upstream code. Never `panic!` on data that originates from user source text.
- [ ] **Every error carries a `Span`.** `ParseError`, `TypeError`, `CodegenError`, and `ModuleError` all include a `Span` for source location. Errors without spans are review failures.
- [ ] **Warnings are data, not side effects.** No `eprintln!` for diagnostics. Accumulate `Vec<Warning>`. Warnings flow to the caller and are displayed by the binary crate only. (Addresses typechecker audit MED-6.)

## 2. Code Structure

These items derive from `src/CLAUDE.md` "Code Structure" and the prototype's primary structural debts (typechecker audit HIGH-1/HIGH-2, codegen audit HIGH-3/HIGH-4/HIGH-5, module audit HIGH-1).

- [ ] **Max ~100 lines per function.** If a function grows beyond this, decompose into named helpers. Long functions are the prototype's #1 structural debt. The prototype had 7 functions exceeding 200 lines, with the worst at 603 lines.
- [ ] **Max 8 parameters per function.** Group related parameters into context structs. The prototype had functions with 21-23 parameters. (Addresses codegen audit LOW-2, cache audit HIGH-3.)
- [ ] **One dispatch method per `Expr` variant.** `infer_expr` and `compile_expr` dispatch to `infer_let`, `infer_apply`, `compile_let`, `compile_apply`, etc. No monolithic match arms. (Addresses typechecker audit HIGH-1.)
- [ ] **Named structs for multi-field returns.** No bare tuples `(Vec<Type>, Type, String)`. Use named structs like `MonoDefn`, `OverloadVariant`, `CompileResult`.
- [ ] **No god objects.** No struct should accumulate responsibilities beyond its core concern. The prototype's `CompiledModule` had 133 references across 18 files. (Addresses module audit, `design/arch/CLAUDE.md` principle 1.)

## 3. Naming and Type Safety

These items derive from `src/CLAUDE.md` "Naming Conventions", `design/arch/CLAUDE.md` "String Newtypes", and module audit MED-2.

- [ ] **String newtypes for all identifiers.** `Symbol`, `ModuleFullPath`, `FQSymbol`, `TraitName`, `TypeName`, `ModuleName`, `JitSymbol`. Never pass bare `String` or `&str` where a typed identifier is expected. The only bare `String` fields allowed are: error messages, documentation strings, source text, user-visible descriptions.
- [ ] **Named constants for magic numbers.** `GOT_TABLE_SIZE`, `NULLARY_TAG_THRESHOLD`, etc. No bare numeric literals in logic. (Addresses codegen audit LOW-1 -- magic number `1024` appeared 8 times.)
- [ ] **Rust naming conventions.** `snake_case` for functions and variables, `CamelCase` for types and enum variants, `SCREAMING_SNAKE` for constants.
- [ ] **Pending work items use named structs.** No bare tuples `(Span, String, String, Type)` for deferred work. Define `PendingMethodCall`, `PendingMonoCall`, etc. (Addresses typechecker audit MED-3.)

## 4. Scope Management

These items derive from `src/CLAUDE.md` "Scope Management" and typechecker audit MED-4.

- [ ] **Scope stack (push/pop), not `env.clone()`.** The prototype cloned `local_env` (~70+ entries) at every scope boundary. Use a stack-based approach: push a scope frame, pop on exit. Lookup traverses top-down.
- [ ] **No leaked scope bindings.** Every `push_scope()` has a corresponding `pop_scope()`. Bindings introduced in a scope are not visible after the scope exits.

## 5. Single Source of Truth

These items derive from `design/arch/CLAUDE.md` principle 7 and findings that appeared across multiple audit files.

- [ ] **One canonical location per concept.** If a concept (ISA flags, heap classification, primitive type names) would exist in two places, it WILL diverge. Every concept gets one authoritative location. The prototype had 3 ISA constructions and 9 duplicate primitive-name mappings.
- [ ] **`Type::from_name()` / `type_name()` for primitive mapping.** No scattered match blocks mapping `"Int" => Type::Int`. (Addresses typechecker audit LOW-1 -- 9 duplicate sites.)
- [ ] **No duplicated logic between batch and REPL paths.** `compile_unit()` with `CompileMode` serves both. If batch and REPL code starts to diverge, escalate to `/arch`. (Addresses cache audit MED-2 -- duplicated import resolution in the cache-load path.)

## 6. Duplication

These items derive from patterns found across all four audit files and from the Sprint 0 cross-plan review.

- [ ] **No copy-pasted blocks.** If two code blocks are structurally identical (same logic, different variable names), extract a shared helper. The prototype had 12+ instances of duplicated blocks exceeding 20 lines.
- [ ] **No near-identical functions.** If two functions share >70% of their logic, unify them with a parameter for the difference. (Addresses typechecker audit MED-1 -- `check_defn`/`check_impl_method` shared 44/48 lines.)
- [ ] **Shared test helpers in one location.** No duplicated test helper functions. The prototype had `tc_with_prelude()` duplicated in 3 files with divergent implementations. (Addresses typechecker audit LOW-4.)
- [ ] **Cross-crate concept tables have a single source of truth.** If the same concept (e.g., operator names, type schemes, IR instructions) is needed by multiple crates, define it once in `cranelisp-types` or `ring0-interfaces.md` and have all crates reference it. Do not maintain parallel lists. (Addresses Sprint 0 review finding: operator tables defined independently in typechecker, backend, and platform plans.)
- [ ] **Result formatting has one owner.** Type-to-display-string logic (`:primitives/Int 3`, `:(Fn [a] a) user/id`) lives in one module, not scattered across crates. Other crates reference it.
- [ ] **Recovery protocols are specified at boundaries.** When two crates interact (typecheck → codegen), the error recovery contract is explicit: what state is rolled back, what is preserved. No silent state corruption on partial failure.

## 7. Architectural Boundaries

These items derive from `design/arch/CLAUDE.md` principles 1-4.

- [ ] **No circular dependencies between crates.** Cargo enforces this at build time, but review that logical dependencies also flow in the correct direction.
- [ ] **Boundary types carry minimum surface area.** `CheckResult` carries exactly what the backend needs -- not the typechecker's internal state. If a boundary type grows fields, review whether they belong.
- [ ] **Cross-skill changes use FIXME protocol.** A skill must NOT silently edit a document owned by another skill. Use `<!-- FIXME(/skill-name): description -->` for proposed changes.
- [ ] **Interface changes require `/arch` review.** Adding or modifying a type in `cranelisp-types` has O(n) impact across skills. Such changes must be coordinated.
- [ ] **Traits used across crate boundaries live in `cranelisp-types`.** If a trait (e.g., `MacroExpander`) needs to be referenced from multiple crates, it must live in the most stable crate. Traits in a downstream crate create hidden coupling.

## 7a. Idiomatic Rust

These items derive from the Sprint 0 cross-plan review and general Rust best practices.

- [ ] **`Display` and `std::error::Error` on error types.** `CranelispError` implements `Display` (for user-facing messages) and `std::error::Error` (for composition). Use `thiserror` or manual impls.
- [ ] **`#[must_use]` on public `Result`-returning functions.** Prevents silent error drops at the API boundary.
- [ ] **Borrow-splitting over clone-to-avoid-borrow.** When a method needs to mutate two fields of `&mut self` simultaneously, pass the fields as explicit parameters rather than cloning one. The prototype's `resolve_one_method` cloned the entire `TypeChecker` to work around this. (Addresses typechecker audit HIGH-3.)
- [ ] **No convenience methods that duplicate authoritative logic.** If `HeapCategory::classify()` is the authoritative heap classification, do not also provide `Type::is_heap()`. Having both creates divergence risk.
- [ ] **Warning types use an enum, not bare strings.** `WarningKind::UnusedVariable`, `WarningKind::ShadowedBinding`, etc. — not `Warning { message: String }`.

## 8. Serialization

These items derive from `src/CLAUDE.md` "Serialization".

- [ ] **Serde derives on all cross-boundary types.** `#[derive(Serialize, Deserialize)]` on types in `cranelisp-types`.
- [ ] **`#[serde(skip)]` for runtime-only fields.** Function pointers, JIT handles, `Duration` -- skip with sensible defaults.

## 9. Testing

These items derive from `src/CLAUDE.md` "Testing" and all four audit files' test coverage findings.

- [ ] **Every module gets `#[cfg(test)] mod tests`.** Unit tests live next to the code they test. The prototype had zero unit tests for 6,192 lines of codegen.
- [ ] **Test names describe behavior, not implementation.** `test_let_polymorphism_infers_identity` not `test_case_47`.
- [ ] **No subsystem at zero test coverage.** Every new module should ship with at least basic unit tests exercising the happy path and one error case.
- [ ] **Integration tests in `tests/`, owned by `/qa`.** Compiler skills write unit tests; `/qa` writes integration tests.

## 10. Performance Awareness

These items derive from typechecker audit MED-7, module audit HIGH-3/MED-4, and codegen audit MED-4/MED-6.

- [ ] **No O(n) scans where a HashMap lookup suffices.** Build indexes for frequent lookups. The prototype had `find_trait_for_method` doing a full symbol scan on every function call site.
- [ ] **No O(n) `Vec::contains` for set membership.** Use `HashSet` when checking membership repeatedly. The prototype used `Vec::contains` for cycle detection in module discovery.
- [ ] **No redundant re-sorting.** Sort once, or use an ordered data structure. The prototype re-sorted a priority queue on every insertion in topological sort.

---

## How to Use This Checklist

1. Before starting a review session, read this checklist as a refresher.
2. For each section, scan the code under review for violations.
3. Record violations as findings with severity (HIGH/MEDIUM/LOW), file path, line number, and a specific recommendation.
4. Report findings to the owning skill.
5. After applying this general checklist, apply the ring-specific checklist for the ring under review.

## Cross-References

- `src/CLAUDE.md` -- the source conventions these items enforce
- `design/arch/CLAUDE.md` -- architectural principles, string newtypes
- `design/review/ring0-checklist.md` -- Ring 0 specific criteria
- `sketch/audits/typechecker.md` -- 21 findings informing this checklist
- `sketch/audits/codegen.md` -- 17 findings informing this checklist
- `sketch/audits/module.md` -- 14 findings informing this checklist
- `sketch/audits/cache.md` -- 15 findings informing this checklist
