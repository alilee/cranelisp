# Ring 0 Review Checklist

Ring 0 specific review criteria. Apply AFTER the general `checklist.md`. Ring 0 property: **Expressions, types, functions, let, if, match (enum-only). No heap allocation, no reference counting.**

Ring 0 exercises: `cranelisp-types`, `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, and the `cranelisp` binary crate (REPL + batch entry points).

---

## 1. Ring 0 Constraints (Mandatory)

These checks enforce the Ring 0 boundary. Violations are automatic HIGH findings.

- [ ] **No heap allocation in compiled code.** Ring 0 types (`Int`, `Bool`, `Float`, enum-only `ADT`, bare `Fn`) are all represented as immediate i64 values. No calls to `cranelisp_alloc` or `cranelisp_free`. No `alloc_func_id` or `free_func_id` in `FnCompiler` or `Jit`.
- [ ] **No reference counting.** No `emit_inc`, `emit_dec`, `pop_scope_for_value`, drop function generation, `HeapCategory` classification in codegen paths, `scope_stack` RC tracking, `consumed_vars`, `borrowed_vars`. Ring 0 values are never heap-allocated, so RC is structurally unnecessary.
- [ ] **No strings as values.** `Type::String` is defined in the `Type` enum (all variants exist from Ring 0) but the AST builder rejects `Sexp::Str` in expression position with a clear error: "strings not yet supported". String literals in docstring position are accepted (they are metadata, not values).
- [ ] **No closures.** Ring 0 lambdas are non-capturing (bare function pointers, no environment). If a lambda would capture a variable from an enclosing scope, the backend emits `CodegenError("function values require closures -- not yet supported")`. No `compile_lambda` with environment allocation.
- [ ] **Enum-only ADTs.** All `TypeDef` constructors have empty `fields` vectors. No data constructors with fields until Ring 1. `ConstructorDef.fields` must be empty in Ring 0. Constructor patterns in `match` have empty `bindings` vectors.
- [ ] **No type parameters on ADTs.** `TypeDef.type_params` is empty. `Type::ADT(name, args)` has an empty `args` vector in Ring 0. Parameterized ADTs (e.g., `Option a`) are Ring 1.
- [ ] **No trait infrastructure.** No `TraitDecl`, `TraitImpl`, `deftrait`, `impl` forms. No trait method resolution. No `ResolvedCall::TraitMethod`, `SigDispatch`, or `AutoCurry`. Operators are hard-wired builtins resolved as `ResolvedCall::BuiltinFn`.
- [ ] **No modules beyond `"user"`.** One implicit module. No `(mod ...)`, `(import ...)`, `(export ...)`, `(platform ...)` forms. No `ModuleGraph`, no `discover()`, no cross-module resolution.
- [ ] **No macros.** No `defmacro`, no `begin` form, no `MacroExpander` calls (Ring 0 uses `NoOpExpander`). The AST builder produces clear errors for macro-related forms.

## 2. Error Handling (Ring 0 Specifics)

Derived from typechecker audit HIGH-4/HIGH-5 and codegen audit MED-1. Ring 0 is the foundation -- if error handling is wrong here, every ring inherits the debt.

- [ ] **`resolve_type_expr` returns `Result`, never panics.** The prototype had 5 `panic!()` calls in type resolution paths reachable from user input. All type resolution in the reimplementation must return `Result<Type, CranelispError>` with spans. (Addresses typechecker audit HIGH-4.)
- [ ] **No `unwrap()` or `expect()` in non-test code.** Review every `.unwrap()` and `.expect()` call. In Ring 0, there are no legitimate uses in pipeline code. `debug_assert!` is acceptable for invariants proven by construction (e.g., "loop header block exists when TCO was set up"). (Addresses typechecker audit HIGH-5, codegen audit MED-1.)
- [ ] **Builtin registration uses `unreachable!` for invariants.** When registering primitives, if a lookup fails on something the code just created (e.g., "primitives module must exist after register_primitives"), use `unreachable!("invariant: primitives module must exist")` rather than `.expect()`. (Addresses typechecker audit HIGH-5 -- `primitives.rs` expects.)
- [ ] **Type errors include the offending types.** A type error message like "type mismatch" is insufficient. Include both types: "expected Int, got Bool at line 3". The `Span` pinpoints the location; the message explains the types.

## 3. Code Structure (Ring 0 Specifics)

Derived from typechecker audit HIGH-1/HIGH-2 and the Wave 2 compiler plans.

- [ ] **`infer_expr` is a thin dispatcher.** The dispatcher function should be ~15 lines: a `match` on `Expr` variants that delegates to `infer_int_lit`, `infer_var`, `infer_let`, `infer_if`, `infer_lambda`, `infer_apply`, `infer_match`, `infer_annotate`, etc. No variant logic inline in the match arm. (Addresses typechecker audit HIGH-1 -- prototype's `infer_expr` was 603 lines.)
- [ ] **`compile_expr` follows the same pattern.** Each `Expr` variant has its own `compile_*` method. No monolithic match arms.
- [ ] **`check_program` is a readable sequence of named phases.** The top-level batch pipeline should read as a ~10-line sequence of named method calls: `register_builtins()`, `register_type_defs()`, `pass1_register_signatures()`, `pass2_check_bodies()`, `build_check_result()`. Each phase is a private method of 20-50 lines. (Addresses typechecker audit HIGH-2 -- prototype's `check_program` was 318 lines with 17 phases.)
- [ ] **`infer_apply` has exactly ONE callee concern in Ring 0.** The prototype had five interleaved callee-inspection blocks. Ring 0 apply analysis checks only for builtin operator resolution. The structure must support adding one concern per ring (Ring 2 adds trait dispatch, constrained fn interception, overload resolution, auto-curry) without interleaving them.
- [ ] **`compile_apply` dispatches to extracted helpers.** Constructor calls, accessor calls, resolved calls, direct calls, and closure calls are each their own method. In Ring 0, only builtin inline primitives and direct/indirect function calls are exercised, but the structure supports clean extension.

## 4. Scope Management (Ring 0 Specifics)

Derived from typechecker audit MED-4 and the typecheck plan section 2.3.

- [ ] **Scope stack implemented from Ring 0.** No `local_env.clone()` at any scope boundary. Lambda bodies, match arms, and `check_defn` all use `push_scope()` / `pop_scope()`. (Addresses typechecker audit MED-4 -- prototype cloned 70+ entry environments per scope.)
- [ ] **`generalize` scans all scopes plus module level.** Free variables that appear in any scope of the stack or in the symbol table are NOT generalized. Only truly free variables become `Scheme.vars`.
- [ ] **Let bindings do not create new scopes.** Per spec 3.5.3, `let` bindings are monomorphic and sequential. Each binding is visible to subsequent bindings in the same scope. The body is in the same scope. Only `lambda`, `match` arms, and `defn` create new scopes.

## 5. Type System (Ring 0 Specifics)

Derived from `design/arch/ring0-interfaces.md` and the typecheck plan.

- [ ] **Full `Type` enum defined from Ring 0.** All variants (`Int`, `Bool`, `String`, `Float`, `Fn`, `ADT`, `Var`, `TyConApp`) exist from the start. Ring 0 exercises a subset; code paths for unexercised variants return appropriate errors or are marked with `// Ring N` comments.
- [ ] **`Type::from_name()` and `type_name()` are the sole primitive mapping.** No other `match name { "Int" => Type::Int, ... }` blocks in the codebase. (Addresses typechecker audit LOW-1.)
- [ ] **`TypeId` is `u32`.** Not `usize`. Narrowed per `src/CLAUDE.md`.
- [ ] **Let-polymorphism at `defn` boundary only.** `(defn id [x] x)` generalizes to `forall [a]. (Fn [a] a)`. `(let [f (fn [x] x)] ...)` gives `f` a monomorphic type. Per spec 3.5.2-3.5.3.
- [ ] **Operator resolution uses polymorphic scheme with validation.** Operators like `+` are registered as `(Fn [a a] a)`. After unification, the resolved type is validated to be `Int` or `Float`. Other types produce a type error. This transitions cleanly to trait constraints in Ring 2.
- [ ] **Exhaustiveness checking is a hard error.** Non-exhaustive match on a concrete ADT type is `CranelispError::TypeError`, not a warning. Per spec 6.5.
- [ ] **No unresolved `Var` reaches codegen.** All `Type::Var(id)` occurrences must be resolved to concrete types by the time `CheckResult` is built. If a `Var` reaches the backend, it is a bug (use `unreachable!`).
- [ ] **`unify()` uses borrow-splitting, not `&mut self`.** `unify` takes explicit `&mut Subst` (and other needed fields) rather than `&mut self`, so callers can borrow `expr_types` or other `TypeChecker` fields independently. Prevents clone-to-avoid-borrow. (Addresses typechecker audit HIGH-3.)
- [ ] **Backend Int/Float disambiguation uses argument span.** When the backend encounters `ResolvedCall::BuiltinFn { name: "+" }`, it determines `iadd` vs `fadd` by looking up the first argument's type in `expr_types` using the argument expression's `Span`. This protocol must be agreed between typechecker and backend.
- [ ] **`CranelispError` implements `Display` and `std::error::Error`.** Not just `Debug`. User-facing error formatting is not ad-hoc.
- [ ] **No `Type::is_heap()` calls in Ring 0 codegen.** Use `HeapCategory::classify()` exclusively. `is_heap()` is a convenience method that disagrees with `classify()` for Ring 0 types (returns `true` for `Fn` and `ADT` even when they are bare i64 values).

## 6. Backend (Ring 0 Specifics)

Derived from the backend plan and codegen audit findings.

- [ ] **Single ISA construction point.** One `build_isa_flags(is_pic: bool)` function. No other code path constructs Cranelift ISA flags. (Addresses cache audit HIGH-2 -- prototype had 3 separate ISA constructions with divergent flags.)
- [ ] **`CodegenContext` separates shared from per-function state.** Shared immutable data (method resolutions, expr types, type defs) in a context struct. Per-function mutable state (builder, variables, TCO) on `FnCompiler`. This prevents the triple-duplication of struct initialization from the prototype. (Addresses codegen audit HIGH-1.)
- [ ] **All i64 ABI.** Every parameter and return value is `AbiParam::new(types::I64)`. No exceptions. One return value per function.
- [ ] **`icmp`/`fcmp` results are `uextend`ed to i64.** Comparison instructions return `i8`. Always extend: `let result = builder.ins().uextend(types::I64, cmp_val)`.
- [ ] **Float operations use `bitcast` through F64.** i64 -> F64 via `bitcast(F64, MemFlags::new(), val)`, operate, F64 -> i64 via `bitcast(I64, MemFlags::new(), result)`.
- [ ] **Block arguments use `BlockArg::Value`.** `jump` and `brif` take `&[BlockArg]`, not `&[Value]`. Always wrap with `BlockArg::Value(val)`.
- [ ] **Loop header NOT sealed eagerly.** TCO creates a loop header block with back-edges from tail calls. Do NOT seal the loop header during body compilation. Use `seal_all_blocks()` after body compilation completes.
- [ ] **Tail position tracking is correct.** Function bodies start with `in_tail_position = true`. `If` branches inherit. `Let` body inherits. `Match` arm bodies inherit. Conditions, binding values, function arguments, and scrutinees are NEVER in tail position. `in_tail_position` is set to `false` before compiling args and restored after. (Addresses a critical correctness requirement -- incorrect tail position leads to stack overflow or incorrect TCO.)
- [ ] **Inline primitive dispatch handles unary and binary.** `not` is unary (1 arg). Arithmetic and comparison are binary (2 args). The dispatch must explicitly handle both arities, not silently skip non-2-arg calls. (Addresses codegen audit LOW-3.)
- [ ] **`NULLARY_TAG_THRESHOLD` is a named constant.** No bare `1024` in codegen. (Addresses codegen audit LOW-1.)

## 7. GOT and Interactive Mode (Ring 0 Specifics)

Derived from the backend plan section 6 and module audit LOW-2.

- [ ] **GOT allocation is per-module.** In Ring 0, one module (`"user"`) means one GOT. The allocation and write paths must be clean enough to extend to multiple modules in Ring 2.
- [ ] **`ensure_got` returns a reference, not Option.** No `unwrap()` after `ensure_got()`. The method should return `&mut [*const u8; GOT_TABLE_SIZE]` directly. (Addresses module audit LOW-2.)
- [ ] **GOT slot assignment is monotonic.** Slots are never reused in Ring 0. Redefinition overwrites the pointer at the existing slot.

## 8. REPL Integration (Ring 0 Specifics)

Derived from `repl/spec.md` and the typecheck plan section 6.

- [ ] **Error recovery does not corrupt state.** A type error in one REPL expression must not leave the `TypeChecker` in an inconsistent state. The substitution, scope stack (which should be empty between inputs), and next_id must be restored on error.
- [ ] **Cross-boundary error recovery: typecheck→codegen.** If codegen fails after successful typechecking, `SymbolTable` entries added during that input must be rolled back. The binary crate snapshots the relevant state before each REPL input and restores on failure. No function name should exist in the symbol table without a corresponding compiled function.
- [ ] **`:Type value` output format.** REPL displays results as `:primitives/Int 42`, `:primitives/Bool true`, `:primitives/Float 3.14`, `:user/Color Color.Red`. Fully-qualified type names. Per `repl/spec.md` section 1.5.
- [ ] **Self-documenting REPL entries.** Special forms (`if`, `let`, `fn`, `defn`, `deftype`, `match`) respond with a description when entered as bare symbols. Constructors respond with their type. Per `repl/spec.md`.
- [ ] **Panic handler uses `panic!()` + `catch_unwind` in Ring 0.** `cranelisp_panic` is a Rust function; the panic propagates through Rust frames only (no JIT frames on the unwind path in Ring 0). The binary crate wraps JIT execution in `catch_unwind`. Ring 1+ requires reassessment (closures introduce JIT→Rust→JIT nesting).

## 9. Frontend (Ring 0 Specifics)

Derived from the frontend plan and spec 01-lexical.md.

- [ ] **Reader parses ALL lexical forms, even non-Ring-0 ones.** Strings, `$name`, `#(...)`, `%1` -- all must parse correctly at the reader level. The AST builder (not the reader) rejects non-Ring-0 forms with clear error messages.
- [ ] **Token precedence follows spec 1.7.** Float before integer before operator. `-3` is an integer, not an operator. `true` requires `!symbol_char()` negative lookahead. `3.14` is a float, not `3` followed by `.14`.
- [ ] **Annotation handling is greedy and context-correct.** `:Int x` in parameter lists means "x has type Int". `:Int 42` in argument lists means `Annotate(Int, 42)`. Both use `try_consume_annotation()`.
- [ ] **`Sexp::Symbol` uses bare `String`, not `Symbol` newtype.** The reader is syntactic, not semantic. The AST builder converts to `Symbol` at the Sexp-to-Expr boundary. Correct layering.
- [ ] **Span uses `Span { start: u32, end: u32 }`, not tuples.** All reader code constructs `Span::new(start as u32, end as u32)`.

## 10. Cross-Crate Consistency (Ring 0 Specifics)

Derived from `design/arch/CLAUDE.md` principles and ring0-interfaces.md.

- [ ] **`CheckResult` fields match specification.** `method_resolutions` (BuiltinFn only), `expr_types`, `warnings`, plus empty/default `constrained_fn_names`, `mono_defns`, `default_method_defns`. No extra fields. No missing fields.
- [ ] **`SymbolTable` has entries for all Ring 0 symbols.** Primitive operators, special forms, user-defined functions, user-defined types, constructors. All accessible via `SymbolTable::get()`.
- [ ] **No type defined in the wrong crate.** `cranelisp-types` is data-only (no logic). All pipeline boundary types live there. Internal types (e.g., `FnCompiler`) live in their owning crate.
- [ ] **`HeapCategory::classify` is correctly implemented for all types.** Even though Ring 0 always returns `NeverHeap`, the function must be correct for `Type::String` (AlwaysHeap), `Type::Fn` with captures (AlwaysHeap -- Ring 1), etc. Later rings depend on this being right from the start.
- [ ] **Single operator table is the source of truth.** Operator names, type schemes, inline IR instructions, and extern wrapper names are defined in ONE location (e.g., `ring0-interfaces.md` or a `RING0_BUILTINS` constant in `cranelisp-types`). The typechecker's `register_builtins()`, backend's `compile_inline_primitive()`, and runtime's operator wrappers all derive from this single table. No parallel lists.
- [ ] **`MacroExpander` trait lives in the correct crate.** If the binary crate injects a `NoOpExpander` into the frontend, the trait must be in `cranelisp-types` (not `cranelisp-frontend`), since the binary crate depends on all library crates but library crates don't depend on each other (except via types).

---

## Ring 0 Acceptance Gate

Before Ring 0 is declared complete, `/review` verifies:

1. **All items on this checklist pass.** Every checkbox is checked or has an explicit waiver with rationale.
2. **All items on `checklist.md` (general) pass.**
3. **Zero HIGH findings outstanding.** Any HIGH finding from review must be resolved before the gate.
4. **MEDIUM findings acknowledged.** Each MEDIUM finding is either resolved or explicitly deferred with rationale in the ring completion report (`ring0-report.md`).
5. **Ring 0 roadmap acceptance criteria pass.** The acceptance criteria from `design/arch/roadmap.md` (lines 24-33) are verified by `/qa`'s integration tests. `/review` confirms the code quality behind those criteria.
6. **`/arch` interface types are clean.** No extra fields, no missing fields, no boundary type mutations beyond specification.

## Cross-References

- `design/review/checklist.md` -- general checklist (apply first)
- `design/review/CLAUDE.md` -- review infrastructure ownership
- `design/arch/ring0-interfaces.md` -- Ring 0 type specifications
- `design/arch/roadmap.md` -- Ring 0 acceptance criteria
- `crates/cranelisp-frontend/plan-frontend.md` -- frontend implementation plan
- `crates/cranelisp-typecheck/plan-typecheck.md` -- typechecker implementation plan
- `crates/cranelisp-backend/plan-backend.md` -- backend implementation plan
- `src/CLAUDE.md` -- source conventions
- `sketch/audits/typechecker.md` -- typechecker audit (HIGH-1 through HIGH-6)
- `sketch/audits/codegen.md` -- codegen audit (HIGH-1 through HIGH-5)
- `sketch/audits/module.md` -- module audit (HIGH-1 through HIGH-3)
- `sketch/audits/cache.md` -- cache audit (HIGH-1 through HIGH-3)
- `spec/ring0-readiness.md` -- spec completeness for Ring 0
- `tests/plan/ring0-readiness.md` -- Ring 0 test coverage assessment

## Next skills

- `/frontend` -- Ring 0 reader and AST builder implementation is the first code to be reviewed against this checklist
- `/typecheck` -- Ring 0 inference engine implementation will exercise the scope management and error handling sections heavily
- `/backend` -- Ring 0 codegen implementation will exercise the backend-specific and GOT sections
- `/qa` -- Ring 0 integration tests validate the acceptance criteria that this checklist's code quality supports
- `/arch` -- Escalation target for architectural boundary violations found during review
