//! Shared `#[cfg(test)]` harness for the backend crate's relocated
//! crate-root tests (FIXME 0495 step 1 — harness extraction).
//!
//! The flat crate-root `src/tests.rs` held ~600 lines of shared scaffolding
//! (`TestCheckResult` + the compile-and-run drivers + side-map enrichment +
//! lifecycle fixture installers + the vec-query value-use kernel) consumed by 73
//! tests. That harness is extracted here as `pub(crate)` items so the
//! per-submodule test homes (`compiler/vec_codegen/tests.rs`,
//! `module_assembly_tests.rs`, `compiler/apply/dispatch_tests.rs`,
//! `compiler/control_flow/fn_as_value/value_use_tests.rs`, the inline
//! `mod tests` in literals/match/lambda/launch/extern_call, and
//! `jit/disasm_tests.rs`) reach it via `use crate::test_support::*`.
//!
//! The re-exports below retain the relocated tests' shared prelude; the fixture
//! builders use the current checked symbol-table lifecycle facades.

// Re-exports so per-submodule test homes get the full prelude the crate-root
// tests relied on via `use super::*` (the original `mod tests` was a child of
// the crate root, so `super::*` resolved lib.rs's scope). These `pub(crate)`
// re-exports reproduce exactly that surface for the relocated homes.
pub(crate) use crate::jit::Jit;
pub(crate) use crate::{CompilationArtifacts, build_isa, compile_to_module, heap, produce_disasm};
pub(crate) use cranelisp_types::{
    CallableTarget, CranelispError, Defn, DefnVariant, DisplayInfo, ErrorLocation, Expr, FQSymbol,
    ModuleFullPath, MonoDefn, Program, Span, Symbol, SymbolTable, TopLevel, Type, Visibility,
};
pub(crate) use dashmap::DashMap;
pub(crate) use std::collections::{HashMap, HashSet};

pub(crate) fn binding_target(module: &ModuleFullPath, name: &Symbol) -> CallableTarget {
    CallableTarget::Binding(FQSymbol {
        module: module.clone(),
        symbol: name.clone(),
    })
}

pub(crate) fn binding_targets(module: &ModuleFullPath, names: &[Symbol]) -> Vec<CallableTarget> {
    names
        .iter()
        .map(|name| binding_target(module, name))
        .collect()
}

pub(crate) fn overload_target(
    module: &ModuleFullPath,
    owner: &str,
    ordinal: usize,
) -> CallableTarget {
    CallableTarget::OverloadArm {
        owner: FQSymbol {
            module: module.clone(),
            symbol: Symbol::from(owner),
        },
        arm: cranelisp_types::CallableArmId::from_ordinal(ordinal)
            .expect("test overload ordinal fits"),
    }
}

pub(crate) fn sig_binding(module: &str, name: &str) -> cranelisp_types::ResolvedCall {
    cranelisp_types::ResolvedCall::SigDispatch {
        target: binding_target(&ModuleFullPath::from(module), &Symbol::from(name)),
    }
}

pub(crate) fn compile_names_to_module<M, C, L>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module: &mut M,
    capture_clif: bool,
) -> Result<CompilationArtifacts, crate::CompilationError>
where
    M: cranelift_module::Module + crate::CodeFinalizer,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let targets = binding_targets(&module_path, names);
    compile_to_module(module_path, &targets, symbol_tables, module, capture_clif)
}

/// Test-only aggregate bridging hand-built `Defn`s through side-map
/// enrichment to the post-Phase-2 backend API. Carries the fields that
/// the boundary `CheckResult` will retire in Wave 2 step 4 (slim-down to
/// `{ warnings, display }`).
///
/// Rationale: per `design/typecheck/ast-annotation.md` §10.2.5, the 20+
/// `#[cfg(test)]` hits that legacy-constructed `CheckResult` literals now
/// use this helper so the Wave 2 slim-down can land cleanly without a
/// red build window. The shape mirrors the current public `CheckResult`
/// field-for-field so the mechanical rewrite is a rename, not a redesign.
pub(crate) struct TestCheckResult {
    // S70: `MethodResolutions` became a struct (resolved_calls +
    // pattern_ctors). The test bridge only ever populated per-span
    // call resolutions, so this field holds the bare `resolved_calls`
    // map shape — exactly what `enrich_defn_from_side_maps` consumes.
    pub(crate) method_resolutions: HashMap<Span, cranelisp_types::ResolvedCall>,
    /// S110 W1 (KC-W0-6): the span-keyed dispatch carriers the backend keyed
    /// reads consume, threaded into each enriched defn's `codegen_view`. Keyed
    /// by the referencing `Var`/`Apply` span → the TERMINAL storage FQ (what the
    /// typecheck producer's `storage_fq()` records). Empty for fixtures whose
    /// bodies drive no keyed dispatch.
    pub(crate) resolved_targets: HashMap<Span, cranelisp_types::FQSymbol>,
    /// S110 W3 (KC-W0-6): the pattern-position ctor sidecar (mirror of the
    /// `MethodResolutions.pattern_ctors` map), keyed by the `Pattern::Constructor`
    /// span → the ctor `Def`'s TERMINAL storage FQ. Threaded into the fixture's
    /// `codegen_view` build so each match arm carries `resolved_ctor`. Required
    /// for any match fixture now that the S19 `lookup_constructor` fallback is
    /// deleted (a carrier-less ctor pattern hard-errors — the production rule).
    pub(crate) pattern_ctors: HashMap<Span, cranelisp_types::FQSymbol>,
    pub(crate) constrained_fn_names: HashSet<Symbol>,
    pub(crate) mono_defns: Vec<MonoDefn>,
    pub(crate) expr_types: HashMap<Span, Type>,
    pub(crate) default_method_defns: Vec<Defn>,
    #[allow(dead_code)]
    pub(crate) warnings: Vec<cranelisp_types::Warning>,
    #[allow(dead_code)]
    pub(crate) display: Option<DisplayInfo>,
}

pub(crate) fn empty_check() -> TestCheckResult {
    TestCheckResult {
        method_resolutions: HashMap::new(),
        resolved_targets: HashMap::new(),
        pattern_ctors: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    }
}

pub(crate) fn empty_tables() -> DashMap<ModuleFullPath, SymbolTable> {
    DashMap::new()
}

/// S111 R4 §1.3 — the CLIF-probe seam (replaces the deleted `Jit::compile_defn`
/// test front door). Compile a single hand-built probe `defn` through the
/// PRODUCTION per-body function `compile_defn_in_module` — the EXACT call
/// `compile_to_module_impl`'s Step 3 makes — and return its rendered CLIF text.
///
/// This is a thin delegator: it declares the intrinsic FuncIds + the probe fn
/// and builds a `CompileContext` the way `compile_to_module_impl` does, so the
/// probe tier stops maintaining a parallel context-assembly (the S107 A.2
/// risk 6 / S110 §2.6 drift the deleted front door caused). It captures CLIF
/// WITHOUT finalizing (matching the old `compile_defn` — no GOT-base
/// registration required for the poll/platform probes). `symbol_tables` must
/// already carry any auxiliary entries (platform effects, callees) the probe
/// body references; the probe `defn` itself is declared here. `resolved_targets`
/// threads the W1 dispatch carriers the keyed reads consume. `extra_decls` are
/// additional user functions declared into `func_ids`, but not compiled, so
/// calls to them resolve through the FuncId tail while only the probe body's
/// CLIF is returned.
pub(crate) fn probe_defn_clif<M, C, L>(
    defn: &Defn,
    extra_decls: &[&Defn],
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: ModuleFullPath,
    module: &mut M,
) -> String
where
    M: cranelift_module::Module,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let clifs = compile_defns_in_module(
        std::slice::from_ref(&defn),
        extra_decls,
        resolved_targets,
        symbol_tables,
        module_path,
        module,
    );
    clifs.into_iter().next().expect("probe: one compiled defn")
}

/// S111 R4 §1.3 — the multi-defn production per-body seam (the core behind
/// [`probe_defn_clif`]). Compiles every defn in `compile` through
/// `compile_defn_in_module` (the EXACT Step-3 call `compile_to_module_impl`
/// makes) onto `module`, declaring `declare_only` fns as well (their FuncIds
/// enter `func_ids` so a declared-only call resolves through the FuncId tail,
/// but their bodies are not emitted). Does NOT finalize — the caller
/// finalizes + runs via its `Jit` for execution-tier tests. Returns the CLIF
/// text of each compiled defn, in order. Preserves each defn's hand-built
/// scheme and parameter types so heap-classification-sensitive tests stay
/// faithful.
pub(crate) fn compile_defns_in_module<M, C, L>(
    compile: &[&Defn],
    declare_only: &[&Defn],
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: ModuleFullPath,
    module: &mut M,
) -> Vec<String>
where
    M: cranelift_module::Module,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    compile_defns_in_module_with_pattern_ctors(
        compile,
        declare_only,
        resolved_targets,
        &HashMap::new(),
        symbol_tables,
        module_path,
        module,
    )
}

/// The constructor-pattern-capable form of [`compile_defns_in_module`].
///
/// The production mono view carries a resolved storage identity for every
/// constructor pattern. Most fixture probes have no constructor pattern and
/// use [`compile_defns_in_module`]'s empty map; an actual pattern-match probe
/// supplies the same span-keyed carrier here rather than re-resolving a name.
pub(crate) fn compile_defns_in_module_with_pattern_ctors<M, C, L>(
    compile: &[&Defn],
    declare_only: &[&Defn],
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
    pattern_ctors: &HashMap<Span, cranelisp_types::FQSymbol>,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: ModuleFullPath,
    module: &mut M,
) -> Vec<String>
where
    M: cranelift_module::Module,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    try_compile_defns_in_module_with_pattern_ctors(
        compile,
        &[],
        declare_only,
        resolved_targets,
        pattern_ctors,
        symbol_tables,
        module_path,
        module,
        &|_| {},
    )
    .expect("probe: compile_defn_in_module")
}

/// The fallible core behind [`compile_defns_in_module`] — same production seam,
/// two additions a probe sometimes needs (S118 W3, FIXME 0893):
///
/// * it RETURNS the `CranelispError` instead of panicking, so a cell can pin a
///   codegen path whose correct outcome is a located refusal (the §6 row-4
///   `BorrowedInvalid` report is one);
/// * `mode_summaries` is positionally aligned with `compile` (shorter/absent ⇒
///   `None`), threading the per-defn [`cranelisp_types::ModeSummary`] that
///   `compile_to_module_impl` reads off each entry's `codegen_view` — the only
///   way a probe can put a parameter in `Borrowed` mode, since
///   `FnCompiler::bind_defn_params` marks params borrowed from the summary and
///   from nothing else.
///
/// There is exactly ONE context assembly (this body); do NOT grow a second.
pub(crate) fn try_compile_defns_in_module<M, C, L>(
    compile: &[&Defn],
    mode_summaries: &[Option<cranelisp_types::ModeSummary>],
    declare_only: &[&Defn],
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: ModuleFullPath,
    module: &mut M,
) -> Result<Vec<String>, CranelispError>
where
    M: cranelift_module::Module,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    try_compile_defns_in_module_with_pattern_ctors(
        compile,
        mode_summaries,
        declare_only,
        resolved_targets,
        &HashMap::new(),
        symbol_tables,
        module_path,
        module,
        &|_| {},
    )
}

/// The fallible core with constructor-pattern carriers: [`try_compile_defns_in_module`]
/// plus the span-keyed `pattern_ctors` map of
/// [`compile_defns_in_module_with_pattern_ctors`].
///
/// `supply_site_facts` edits each built body before compilation. It stands in
/// for the typecheck site facts (`escapes`, `confined`, …) that a hand-built
/// `Expr` cannot carry.
#[allow(clippy::too_many_arguments)]
pub(crate) fn try_compile_defns_in_module_with_pattern_ctors<M, C, L>(
    compile: &[&Defn],
    mode_summaries: &[Option<cranelisp_types::ModeSummary>],
    declare_only: &[&Defn],
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
    pattern_ctors: &HashMap<Span, cranelisp_types::FQSymbol>,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module_path: ModuleFullPath,
    module: &mut M,
    supply_site_facts: &dyn Fn(&mut cranelisp_types::MonoExpr),
) -> Result<Vec<String>, CranelispError>
where
    M: cranelift_module::Module,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    use cranelift::prelude::{AbiParam, FunctionBuilderContext, types};
    use cranelift_module::{Linkage, Module};

    let intrinsic_ids =
        crate::jit::declare_intrinsics_generic(module).expect("probe: declare intrinsics");

    // Declare every fn (Linkage::Local, bare name) — the Step-2 shape.
    let mut func_ids: HashMap<Symbol, cranelift_module::FuncId> = HashMap::new();
    let mut func_arities: HashMap<Symbol, usize> = HashMap::new();
    for d in compile.iter().copied().chain(declare_only.iter().copied()) {
        let mut sig = module.make_signature();
        for _ in d.params() {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(d.name.as_ref(), Linkage::Local, &sig)
            .expect("probe: declare fn");
        func_ids.insert(d.name.clone(), func_id);
        func_arities.insert(d.name.clone(), d.params().len());
    }

    // S0: the probe seam owns a registry for the duration of the probe, exactly
    // as `compile_to_module_impl` owns one across Step 3. Its `finish()` fence is
    // not run here — the probe does not project artifacts.
    let mut glue = crate::drop_glue::DropGlueRegistry::new(
        module_path.clone(),
        intrinsic_ids
            .dealloc
            .expect("probe: runtime/dealloc declared"),
        intrinsic_ids.vec_drop,
    );

    let mut func_ctx = FunctionBuilderContext::new();
    let mut clifs = Vec::with_capacity(compile.len());
    for (i, d) in compile.iter().enumerate() {
        // Lenient body with the dispatch carriers — mirrors the `codegen_view`
        // `compile_to_module` builds for a hand-constructed fixture (KC-W0-6):
        // strict `from_expr` first, `lenient_from_expr` fallback. S114 carrier
        // flip: `from_expr` now takes the TOTAL typed maps, derived from the
        // fixture's `resolved_targets` (present ⇒ Global/Dispatch, absent ⇒
        // Local/ViaCallee).
        let (var_refs, apply_refs) = resolved_targets_to_typed_maps(d.body(), resolved_targets);
        let mut body =
            cranelisp_types::MonoExpr::from_expr(d.body(), pattern_ctors, &var_refs, &apply_refs)
                .unwrap_or_else(|_| {
                    cranelisp_types::MonoExpr::lenient_from_expr(
                        d.body(),
                        pattern_ctors,
                        &var_refs,
                        &apply_refs,
                    )
                });
        supply_site_facts(&mut body);
        let compile_ctx = crate::compiler::CompileContext {
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables,
            current_module: module_path.clone(),
            alloc_func_id: intrinsic_ids.alloc,
            dealloc_func_id: intrinsic_ids
                .dealloc
                .expect("probe: runtime/dealloc declared"),
            alloc_string_func_id: intrinsic_ids.alloc_string,
            panic_func_id: intrinsic_ids.panic,
            vec_new_func_id: intrinsic_ids.vec_new,
            vec_drop_func_id: intrinsic_ids.vec_drop,
        };
        // Production carries these types from the already-selected callable
        // arm. Hand-built probes recover the same fixture-owned scheme here.
        let param_types = symbol_tables
            .get(&module_path)
            .and_then(|table| {
                table
                    .get(d.name.as_ref())
                    .and_then(cranelisp_types::Binding::callable)
                    .and_then(|callable| match &callable.arm.scheme.ty {
                        Type::Fn(params, _) => {
                            Some(params.iter().cloned().map(Some).collect::<Vec<_>>())
                        }
                        _ => None,
                    })
            })
            .unwrap_or_else(|| vec![None; d.params().len()]);
        let art = crate::compile_defn_in_module(
            d,
            &body,
            mode_summaries.get(i).cloned().flatten(),
            &param_types,
            module,
            &mut func_ctx,
            &func_ids,
            compile_ctx,
            true,
            &mut glue,
        )?;
        clifs.push(art.clif_ir);
    }
    Ok(clifs)
}

/// S114 carrier flip (`typed-resolution-carrier.md` §4): build the TOTAL typed
/// `var_refs`/`apply_refs` maps a hand-built fixture body needs for
/// `MonoExpr::from_expr` (now total-or-`ViewBuildError`), from the legacy
/// span→`FQSymbol` `resolved_targets` map every backend fixture already threads.
///
/// A `Var`/`Apply` span PRESENT in `resolved_targets` is a table-resolved
/// reference — `VarRef::Global`/`ApplyRef::Dispatch` with the recorded storage
/// FQ. An ABSENT span is a local / no-dispatch reference — `VarRef::Local
/// { binder, binding_span: SYNTHETIC }` / `ApplyRef::ViaCallee`, the neutral
/// positive verdict. This preserves the exact pre-flip dispatch semantics the
/// fixtures rely on: an absent span that is genuinely a `variables` local wins
/// the backend scope-stack read first (KC-N6); an absent unresolved global falls
/// through to the same loud carrier-miss hard error the production rule raises.
pub(crate) fn resolved_targets_to_typed_maps(
    expr: &Expr,
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
) -> (
    HashMap<Span, cranelisp_types::VarRef>,
    HashMap<Span, cranelisp_types::ApplyRef>,
) {
    let mut var_refs = HashMap::new();
    let mut apply_refs = HashMap::new();
    fill_typed_maps(expr, resolved_targets, &mut var_refs, &mut apply_refs);
    (var_refs, apply_refs)
}

fn fill_typed_maps(
    expr: &Expr,
    rt: &HashMap<Span, cranelisp_types::FQSymbol>,
    var_refs: &mut HashMap<Span, cranelisp_types::VarRef>,
    apply_refs: &mut HashMap<Span, cranelisp_types::ApplyRef>,
) {
    use cranelisp_types::{ApplyRef, VarRef};
    match expr {
        Expr::Var { name, span, .. } => {
            let vr = match rt.get(span) {
                Some(fq) => VarRef::Global(fq.clone()),
                None => VarRef::Local {
                    binder: name.clone(),
                    binding_span: Span::SYNTHETIC,
                },
            };
            var_refs.insert(*span, vr);
        }
        Expr::Apply {
            callee, args, span, ..
        } => {
            let ar = match rt.get(span) {
                Some(fq) => ApplyRef::Dispatch(fq.clone()),
                None => ApplyRef::ViaCallee,
            };
            apply_refs.insert(*span, ar);
            fill_typed_maps(callee, rt, var_refs, apply_refs);
            for a in args {
                fill_typed_maps(a, rt, var_refs, apply_refs);
            }
        }
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, v) in bindings {
                fill_typed_maps(v, rt, var_refs, apply_refs);
            }
            fill_typed_maps(body, rt, var_refs, apply_refs);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            fill_typed_maps(cond, rt, var_refs, apply_refs);
            fill_typed_maps(then_branch, rt, var_refs, apply_refs);
            fill_typed_maps(else_branch, rt, var_refs, apply_refs);
        }
        Expr::Lambda { body, .. }
        | Expr::Trace { body, .. }
        | Expr::Annotate { expr: body, .. } => {
            fill_typed_maps(body, rt, var_refs, apply_refs);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            fill_typed_maps(scrutinee, rt, var_refs, apply_refs);
            for arm in arms {
                fill_typed_maps(&arm.body, rt, var_refs, apply_refs);
            }
        }
        Expr::VecLit { elements, .. } => {
            for e in elements {
                fill_typed_maps(e, rt, var_refs, apply_refs);
            }
        }
        Expr::ConstrADT { fields, .. } => {
            for f in fields {
                fill_typed_maps(f, rt, var_refs, apply_refs);
            }
        }
        Expr::LaunchContinue {
            launched,
            continuation,
            ..
        } => {
            fill_typed_maps(launched, rt, var_refs, apply_refs);
            fill_typed_maps(continuation, rt, var_refs, apply_refs);
        }
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. } => {}
    }
}

/// Read a Vec's `len` field directly from its base pointer.
///
/// Local-only inline of the user-callable `vec-len` primitive's body —
/// kept inside the backend test module to avoid the dep edge
/// `cranelisp-backend → cranelisp-primitives` (forbidden by Decision
/// 0048 §"Structural invariant — backend dep-ban", S68 Wave 4). The Vec
/// layout is fixed by Decision 11: `[size@+0 | rc@+8 | len@+16 | cap@+24 | data_ptr@+32]`.
///
/// SAFETY: `ptr` MUST be a valid Vec base pointer (heap allocation
/// whose +16 offset is a populated `i64` len field).
pub(crate) fn vec_len_for_test(ptr: i64) -> i64 {
    unsafe { *((ptr as *const u8).add(16) as *const i64) }
}

/// Test helper: enrich a defn's AST nodes with type and resolution
/// annotations from CheckResult side maps.
///
/// Used by tests that build ASTs by hand and carry resolutions in a
/// `CheckResult`. In production, typecheck annotates the AST directly,
/// so this bridge is test-only.
pub(crate) fn enrich_defn_from_side_maps(
    defn: &mut Defn,
    resolutions: &HashMap<Span, cranelisp_types::ResolvedCall>,
    expr_types: &HashMap<Span, Type>,
) {
    for variant in &mut defn.variants {
        enrich_expr_from_side_maps(&mut variant.body, resolutions, expr_types);
        // S84 Phase 3 (FIXME 0391): the backend codegen walk is over
        // `MonoExpr`, which requires a CONCRETE type on every node. Real
        // typecheck guarantees that; these legacy test fixtures often leave
        // literal/leaf nodes un-annotated (`inferred_type: None`) or carry a
        // residual `Var`. Fill any such node with a best-effort concrete type
        // so `MonoExpr::from_expr` succeeds — test-only scaffolding that
        // stands in for the typecheck mono-population seam.
        concretize_test_body(&mut variant.body);
    }
}

/// Test-only: fill every node's `inferred_type` with a concrete `Type` so the
/// `MonoExpr` codegen view can be built. Literals take their structural type;
/// any other node lacking a concrete annotation defaults to `Type::Int` (these
/// fixtures are scalar-result i64 probes — the heap classification a node's
/// type drives is `NeverHeap` for `Int`, which is the correct default for the
/// untyped scalar paths these tests exercise; tests that need a heap type set
/// it explicitly via the side maps, which run first and are preserved).
pub(crate) fn concretize_test_body(expr: &mut Expr) {
    use cranelisp_types::Expr;
    // Recurse into children first.
    match expr {
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, v) in bindings {
                concretize_test_body(v);
            }
            concretize_test_body(body);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            concretize_test_body(cond);
            concretize_test_body(then_branch);
            concretize_test_body(else_branch);
        }
        Expr::Lambda { body, .. }
        | Expr::Trace { body, .. }
        | Expr::Annotate { expr: body, .. } => {
            concretize_test_body(body);
        }
        Expr::Apply { callee, args, .. } => {
            concretize_test_body(callee);
            for a in args {
                concretize_test_body(a);
            }
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            concretize_test_body(scrutinee);
            for arm in arms {
                concretize_test_body(&mut arm.body);
            }
        }
        Expr::VecLit { elements, .. } => {
            for e in elements {
                concretize_test_body(e);
            }
        }
        Expr::ConstrADT { fields, .. } => {
            for f in fields {
                concretize_test_body(f);
            }
        }
        Expr::LaunchContinue {
            launched,
            continuation,
            ..
        } => {
            concretize_test_body(launched);
            concretize_test_body(continuation);
        }
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
    }
    // Determine the structural fallback for THIS node.
    let structural = match expr {
        Expr::IntLit { .. } => Some(Type::Int),
        Expr::FloatLit { .. } => Some(Type::Float),
        Expr::BoolLit { .. } => Some(Type::Bool),
        Expr::StringLit { .. } => Some(Type::String),
        _ => None,
    };
    // Fill the node iff it has no concrete type yet (None or a residual Var).
    let needs_fill = match expr.inferred_type() {
        None => true,
        Some(ty) => !ty.is_concrete(),
    };
    if needs_fill {
        let fill = structural.unwrap_or(Type::Int);
        expr.set_inferred_type(Some(Box::new(fill)));
    }
}

/// Test helper: recursively enrich expression nodes with side map data.
pub(crate) fn enrich_expr_from_side_maps(
    expr: &mut cranelisp_types::Expr,
    resolutions: &HashMap<Span, cranelisp_types::ResolvedCall>,
    expr_types: &HashMap<Span, Type>,
) {
    use cranelisp_types::Expr;

    let span = expr.span();

    // Overlay inferred_type from side map if present.
    if let Some(ty) = expr_types.get(&span) {
        expr.set_inferred_type(Some(Box::new(ty.clone())));
    }

    // Overlay resolved_call from side map if present (Apply only).
    if let Expr::Apply {
        resolved_call,
        span: apply_span,
        ..
    } = expr
        && let Some(resolution) = resolutions.get(apply_span)
    {
        *resolved_call = Some(Box::new(resolution.clone()));
    }

    // Recurse into children.
    match expr {
        Expr::Let { bindings, body, .. } => {
            for (_, binding_expr) in bindings {
                enrich_expr_from_side_maps(binding_expr, resolutions, expr_types);
            }
            enrich_expr_from_side_maps(body, resolutions, expr_types);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            enrich_expr_from_side_maps(cond, resolutions, expr_types);
            enrich_expr_from_side_maps(then_branch, resolutions, expr_types);
            enrich_expr_from_side_maps(else_branch, resolutions, expr_types);
        }
        Expr::Lambda { body, .. } => {
            enrich_expr_from_side_maps(body, resolutions, expr_types);
        }
        Expr::Apply { callee, args, .. } => {
            enrich_expr_from_side_maps(callee, resolutions, expr_types);
            for arg in args {
                enrich_expr_from_side_maps(arg, resolutions, expr_types);
            }
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            enrich_expr_from_side_maps(scrutinee, resolutions, expr_types);
            for arm in arms {
                enrich_expr_from_side_maps(&mut arm.body, resolutions, expr_types);
            }
        }
        Expr::VecLit { elements, .. } => {
            for elem in elements {
                enrich_expr_from_side_maps(elem, resolutions, expr_types);
            }
        }
        Expr::Annotate { expr: inner, .. } => {
            enrich_expr_from_side_maps(inner, resolutions, expr_types);
        }
        Expr::Trace { body, .. } => {
            enrich_expr_from_side_maps(body, resolutions, expr_types);
        }
        Expr::ParBind { bindings, body, .. } => {
            for (_, binding_expr) in bindings {
                enrich_expr_from_side_maps(binding_expr, resolutions, expr_types);
            }
            enrich_expr_from_side_maps(body, resolutions, expr_types);
        }
        Expr::ConstrADT { fields, .. } => {
            for f in fields {
                enrich_expr_from_side_maps(f, resolutions, expr_types);
            }
        }
        Expr::LaunchContinue {
            launched,
            continuation,
            ..
        } => {
            enrich_expr_from_side_maps(launched, resolutions, expr_types);
            enrich_expr_from_side_maps(continuation, resolutions, expr_types);
        }
        // Leaf nodes: no children to recurse into.
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => {}
    }
}

/// Install a concrete body fixture through the lifecycle-owned slot mint.
pub(crate) fn install_def_entry(table: &mut SymbolTable, defn: Defn) -> usize {
    install_def_entry_inner(table, defn, None, &HashMap::new(), &HashMap::new())
}

/// Install a concrete body through the lifecycle-owned slot mint and thread W1
/// dispatch carriers (KC-W0-6) into its `codegen_view`, so keyed call reads see
/// each Apply/callee `resolved_target`.
pub(crate) fn install_def_entry_with_targets(
    table: &mut SymbolTable,
    defn: Defn,
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
) -> usize {
    install_def_entry_inner(table, defn, None, &HashMap::new(), resolved_targets)
}

/// Install a concrete body and assert that the lifecycle mint selected the
/// expected GOT slot. Used where slot order is part of the test fixture.
pub(crate) fn install_def_entry_at_slot(
    table: &mut SymbolTable,
    defn: Defn,
    expected_slot: usize,
) -> usize {
    install_def_entry_inner(
        table,
        defn,
        Some(expected_slot),
        &HashMap::new(),
        &HashMap::new(),
    )
}

/// Install a concrete body, assert its lifecycle-minted GOT slot, and thread
/// W1 dispatch carriers (KC-W0-6) into its `codegen_view`. `resolved_targets`
/// maps each call/callee span to the terminal storage FQ (for example, an
/// imported platform effect's home rather than the caller's alias).
pub(crate) fn install_def_entry_at_slot_with_targets(
    table: &mut SymbolTable,
    defn: Defn,
    expected_slot: usize,
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
) -> usize {
    install_def_entry_inner(
        table,
        defn,
        Some(expected_slot),
        &HashMap::new(),
        resolved_targets,
    )
}

pub(crate) fn install_def_entry_inner(
    table: &mut SymbolTable,
    defn: Defn,
    expected_slot: Option<usize>,
    pattern_ctors: &HashMap<Span, cranelisp_types::FQSymbol>,
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
) -> usize {
    use cranelisp_types::{
        CallableOrigin, MonoDefnVariant, MonoExpr, Realization, Scheme, Visibility,
    };
    let param_count = defn.params().len();
    // `param_names` is `Vec<Symbol>`; the fused `params` tuples carry the
    // optional annotation, so project out the names.
    let param_names: Vec<Symbol> = defn
        .variants
        .first()
        .map(|v| v.params.iter().map(|(n, _)| n.clone()).collect())
        .unwrap_or_default();
    let scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Fn(
            (0..param_count).map(|_| Type::Int).collect(),
            Box::new(Type::Int),
        ),
    };
    // `ast` is `Option<DefnVariant>` post-narrowing — store the single
    // meaningful variant. Concretize the body (test scaffolding for the
    // typecheck mono-population seam — FIXME 0391) so the codegen view builds.
    let variant = defn.variants.first().cloned().map(|mut v| {
        concretize_test_body(&mut v.body);
        v
    });
    let codegen_view = variant.as_ref().map(|v| {
        // W3 (KC-W0-6): thread the `pattern_ctors` sidecar so a fixture with a
        // ctor pattern arm carries its `MonoMatchArm.resolved_ctor` — the S19
        // None-arm `lookup_constructor` fallback is deleted, so a pattern ctor
        // with no carrier now hard-errors at codegen (the production discipline).
        let (var_refs, apply_refs) = resolved_targets_to_typed_maps(&v.body, resolved_targets);
        let body = MonoExpr::from_expr(&v.body, pattern_ctors, &var_refs, &apply_refs)
            .expect("test fixture body concretizes for the codegen view (FIXME 0391)");
        MonoDefnVariant {
            name: defn.name.clone(),
            params: v.params.iter().map(|(n, _)| n.clone()).collect(),
            body,
            span: v.span,
            mode_summary: None,
        }
    });
    let variant = variant.expect("test defn has one variant");
    let slot = table
        .install_concrete(
            defn.name.clone(),
            scheme,
            param_names,
            None,
            0,
            CallableOrigin::Plain,
            Realization::Body {
                view: codegen_view.expect("concrete fixture has a codegen view"),
                code: None,
            },
            Some(variant),
            vec![],
            Visibility::Public,
        )
        .expect("install concrete test fixture")
        .index();
    if let Some(expected) = expected_slot {
        assert_eq!(slot, expected, "test fixture slot order");
    }
    slot
}

pub(crate) fn install_overloaded_entry(
    table: &mut SymbolTable,
    mut defn: Defn,
    schemes: Vec<cranelisp_types::Scheme>,
    check: &TestCheckResult,
) {
    enrich_defn_from_side_maps(&mut defn, &check.method_resolutions, &check.expr_types);
    assert_eq!(
        defn.variants.len(),
        schemes.len(),
        "each overload fixture variant needs one authoritative scheme",
    );
    let arms = defn
        .variants
        .iter()
        .cloned()
        .zip(schemes)
        .map(|(mut variant, scheme)| {
            concretize_test_body(&mut variant.body);
            let view = test_codegen_view(&defn.name, &variant, &check.resolved_targets);
            cranelisp_types::CallableArmDraft::concrete_body(
                scheme,
                variant
                    .params
                    .iter()
                    .map(|(name, _)| name.clone())
                    .collect(),
                variant,
                view,
                Vec::new(),
            )
        })
        .collect();
    table
        .install_overloaded(defn.name, defn.docstring, 0, arms, defn.visibility)
        .expect("install overloaded fixture");
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn install_ctor_fixture(
    table: &mut SymbolTable,
    name: Symbol,
    scheme: cranelisp_types::Scheme,
    param_names: Vec<Symbol>,
    type_name: cranelisp_types::FQTypeName,
    tag: usize,
    field_count: usize,
    type_def: Option<Box<cranelisp_types::TypeDefInfo>>,
    ast: Option<DefnVariant>,
    view: Option<cranelisp_types::MonoDefnVariant>,
) -> usize {
    use cranelisp_types::{CallableOrigin, ConcreteType, MonoExpr, Realization};

    let view = view.unwrap_or_else(|| cranelisp_types::MonoDefnVariant {
        name: name.clone(),
        params: param_names.clone(),
        body: MonoExpr::IntLit {
            value: tag as i64,
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        },
        span: Span::SYNTHETIC,
        mode_summary: None,
    });
    table
        .install_concrete(
            name,
            scheme,
            param_names,
            None,
            tag as u64,
            CallableOrigin::Ctor {
                type_name,
                tag,
                field_count,
                internal: false,
                type_def,
            },
            Realization::Body { view, code: None },
            ast,
            vec![],
            Visibility::Public,
        )
        .expect("install constructor fixture")
        .index()
}

pub(crate) fn install_type_fixture(
    table: &mut SymbolTable,
    name: Symbol,
    info: cranelisp_types::TypeDefInfo,
) {
    use cranelisp_types::{Binding, Decl, TypeRecord};
    table
        .install_binding(
            name,
            Binding::new(
                Decl::Type(TypeRecord::Defined {
                    info,
                    docstring: None,
                }),
                Visibility::Public,
            ),
        )
        .expect("install type fixture");
}

/// Build a `codegen_view` for a HAND-CONSTRUCTED fixture entry (KC-W0-6, S110
/// W0.b `backend-keyed-consumer.md` §4 W0.b). After the totalization flip the
/// backend hard-errors on a codegen-reached body with `codegen_view: None`, so
/// every hand-built fixture that reaches `compile_to_module` MUST carry a view —
/// the same obligation the typecheck producer satisfies for real programs.
///
/// TOTAL, mirroring `program::support::build_concrete_codegen_view`: strict
/// `MonoExpr::from_expr` first, [`MonoExpr::lenient_from_expr`] fallback — so a
/// synthetic ctor/accessor-style body (un-annotated `inferred_type: None` nodes)
/// still yields a view. `resolved_targets` threads the W1 dispatch carriers a
/// fixture computes directly from the tables it also builds (empty for
/// value-only fixtures — carriers ride unread until W1 flips the keyed reads).
pub(crate) fn test_codegen_view(
    name: &Symbol,
    variant: &cranelisp_types::DefnVariant,
    resolved_targets: &HashMap<Span, cranelisp_types::FQSymbol>,
) -> cranelisp_types::MonoDefnVariant {
    let empty_ctors = HashMap::new();
    let (var_refs, apply_refs) = resolved_targets_to_typed_maps(&variant.body, resolved_targets);
    let body =
        cranelisp_types::MonoExpr::from_expr(&variant.body, &empty_ctors, &var_refs, &apply_refs)
            .unwrap_or_else(|_| {
                cranelisp_types::MonoExpr::lenient_from_expr(
                    &variant.body,
                    &empty_ctors,
                    &var_refs,
                    &apply_refs,
                )
            });
    cranelisp_types::MonoDefnVariant {
        name: name.clone(),
        params: variant.params.iter().map(|(n, _)| n.clone()).collect(),
        body,
        span: variant.span,
        mode_summary: None,
    }
}

/// KC-W0-6 (S110 W1): produce the span-keyed dispatch carriers a hand-built
/// CLIF-probe fixture needs after the W1 flip. Walk `body`; for every `Apply`
/// whose callee is a bare `Var` named in `user_fns`, map BOTH the `Apply` span
/// AND the callee-`Var` span to `<module>/<name>` — the FQ the fixture stored
/// the entry under. Mirrors the typecheck producer's per-reference resolution
/// for the closed world the fixture builds by hand (one module, no import
/// chains, so the storage key IS the written name). Names NOT in `user_fns`
/// (locals, inline-primitive `BuiltinFn` callees) are left un-carried.
pub(crate) fn call_carriers(
    body: &Expr,
    module: &ModuleFullPath,
    user_fns: &[&str],
) -> HashMap<Span, cranelisp_types::FQSymbol> {
    let mut out = HashMap::new();
    collect_call_carriers(body, module, user_fns, &mut out);
    out
}

fn collect_call_carriers(
    e: &Expr,
    module: &ModuleFullPath,
    user_fns: &[&str],
    out: &mut HashMap<Span, cranelisp_types::FQSymbol>,
) {
    if let Expr::Apply { callee, span, .. } = e
        && let Expr::Var {
            name, span: cspan, ..
        } = &**callee
        && user_fns.contains(&name.as_ref())
    {
        let fq = cranelisp_types::FQSymbol {
            module: module.clone(),
            symbol: name.clone(),
        };
        out.insert(*span, fq.clone());
        out.insert(*cspan, fq);
    }
    match e {
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, v) in bindings {
                collect_call_carriers(v, module, user_fns, out);
            }
            collect_call_carriers(body, module, user_fns, out);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_call_carriers(cond, module, user_fns, out);
            collect_call_carriers(then_branch, module, user_fns, out);
            collect_call_carriers(else_branch, module, user_fns, out);
        }
        Expr::Lambda { body, .. }
        | Expr::Trace { body, .. }
        | Expr::Annotate { expr: body, .. } => {
            collect_call_carriers(body, module, user_fns, out);
        }
        Expr::Apply { callee, args, .. } => {
            collect_call_carriers(callee, module, user_fns, out);
            for a in args {
                collect_call_carriers(a, module, user_fns, out);
            }
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            collect_call_carriers(scrutinee, module, user_fns, out);
            for arm in arms {
                collect_call_carriers(&arm.body, module, user_fns, out);
            }
        }
        Expr::VecLit { elements, .. } => {
            for el in elements {
                collect_call_carriers(el, module, user_fns, out);
            }
        }
        Expr::ConstrADT { fields, .. } => {
            for f in fields {
                collect_call_carriers(f, module, user_fns, out);
            }
        }
        Expr::LaunchContinue {
            launched,
            continuation,
            ..
        } => {
            collect_call_carriers(launched, module, user_fns, out);
            collect_call_carriers(continuation, module, user_fns, out);
        }
        _ => {}
    }
}

/// S110 W2 (KC-K8): record the carrier for every **value-position** vec-query
/// primitive `Var` (`vec-get`/`vec-set`/`vec-push` named as a value, not called)
/// — its span → `{primitives, <name>}`, the storage FQ the producer records.
/// The value seam's `is_known_function` / `is_inline_primitive_at` keyed reads
/// consume it. A vec-query name in CALLEE position keys off the Apply carrier
/// (or the `BuiltinFn` arm's self-constructed FQ) instead, so this deliberately
/// records ALL `vec-*` Var spans — a callee that also gets a carrier here is
/// harmless (the keyed read agrees).
fn collect_vec_query_value_carriers(e: &Expr, out: &mut HashMap<Span, cranelisp_types::FQSymbol>) {
    if let Expr::Var { name, span, .. } = e
        && matches!(
            name.as_ref(),
            "vec-get" | "vec-set" | "vec-push" | "vec-len"
        )
    {
        out.insert(
            *span,
            cranelisp_types::FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: name.clone(),
            },
        );
    }
    match e {
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, v) in bindings {
                collect_vec_query_value_carriers(v, out);
            }
            collect_vec_query_value_carriers(body, out);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_vec_query_value_carriers(cond, out);
            collect_vec_query_value_carriers(then_branch, out);
            collect_vec_query_value_carriers(else_branch, out);
        }
        Expr::Lambda { body, .. }
        | Expr::Trace { body, .. }
        | Expr::Annotate { expr: body, .. } => {
            collect_vec_query_value_carriers(body, out);
        }
        Expr::Apply { callee, args, .. } => {
            collect_vec_query_value_carriers(callee, out);
            for a in args {
                collect_vec_query_value_carriers(a, out);
            }
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            collect_vec_query_value_carriers(scrutinee, out);
            for arm in arms {
                collect_vec_query_value_carriers(&arm.body, out);
            }
        }
        Expr::VecLit { elements, .. } => {
            for el in elements {
                collect_vec_query_value_carriers(el, out);
            }
        }
        Expr::ConstrADT { fields, .. } => {
            for f in fields {
                collect_vec_query_value_carriers(f, out);
            }
        }
        _ => {}
    }
}

/// Declare a minimal slotless callable through the lifecycle facade so the W1
/// keyed read (`entry_at`) hits for a fixture whose callee exists only as a
/// declaration and `FuncId`. `compile_direct_call` therefore reaches its
/// `FuncId` tail; the table binding exists only to prevent a keyed-read miss.
pub(crate) fn insert_user_fn_stub(table: &mut SymbolTable, name: &str, arity: usize) {
    let params: Vec<Type> = (0..arity).map(|_| Type::Int).collect();
    insert_user_fn_stub_typed(table, name, &params, Type::Int);
}

/// [`insert_user_fn_stub`] with EXPLICIT parameter types. The all-`Int` stamp is
/// the right default for scalar dispatch probes, but the entry's `Scheme.ty` is
/// also the authoritative source `FnCompiler::bind_defn_params` reads parameter
/// types from (`defn_param_types`), so a probe whose behaviour depends on a
/// param being heap-typed MUST spell the type here — a `String` param stamped
/// `Int` is never heap-classified and every RC gate silently sits out.
pub(crate) fn insert_user_fn_stub_typed(
    table: &mut SymbolTable,
    name: &str,
    param_types: &[Type],
    return_type: Type,
) {
    use cranelisp_types::{CallableOrigin, Scheme};
    let arity = param_types.len();
    let scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: Type::Fn(param_types.to_vec(), Box::new(return_type)),
    };
    table
        .declare(
            Symbol::from(name),
            scheme,
            (0..arity).map(|i| Symbol::from(format!("p{i}"))).collect(),
            None,
            0,
            CallableOrigin::Plain,
            Visibility::Public,
        )
        .expect("declare test callable stub");
}

/// Test helper: wrap an expression in a synthetic zero-arg defn, compile via
/// `compile_to_module`, finalize JIT, execute, and return the i64 result.
///
/// The `check` parameter provides side-map data that is enriched onto the
/// defn's AST nodes before compilation (bridging old test code to the new
/// CheckResult-free API).
pub(crate) fn test_compile_and_run(
    expr: &Expr,
    check: &TestCheckResult,
    tables: &DashMap<ModuleFullPath, SymbolTable>,
) -> Result<i64, CranelispError> {
    let mut defn = Defn {
        name: Symbol::from("__expr__"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: expr.clone(),
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    // Enrich the defn from CheckResult side maps (test bridge).
    enrich_defn_from_side_maps(&mut defn, &check.method_resolutions, &check.expr_types);

    let module = ModuleFullPath::from("user");
    let name = defn.name.clone();
    // Post-Phase-2: insert the defn into the shared symbol table so the
    // backend's `compile_to_module` reads its AST from there.
    {
        let mut st = tables
            .entry(module.clone())
            .or_insert_with(|| SymbolTable::new(module.clone()));
        install_def_entry_inner(
            &mut st,
            defn,
            None,
            &check.pattern_ctors,
            &check.resolved_targets,
        );
    }

    let mut jit = Jit::new(tables)?;
    let _artifacts = compile_names_to_module(
        module.clone(),
        std::slice::from_ref(&name),
        tables,
        jit.jit_module(),
        true,
    )?;
    // `compile_to_module` finalizes the JIT internally. The concrete fixture
    // owns a lifecycle-minted slot, while this helper invokes the entry symbol
    // directly by name.
    let ptr = jit.get_ptr_by_name(&name, 0)?;
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    let value = func();
    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        return Err(CranelispError::CodegenError {
            message: format!("runtime panic: {}", msg),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }
    Ok(value)
}

/// Test helper: compile a program via `compile_to_module`, finalize JIT,
/// execute entry function, and return the i64 result.
///
/// Enriches defns from `check` side maps, settles each defn as a concrete body
/// binding with an introspection AST, then hands the name list to
/// `compile_to_module`. Bridges the test scaffolding to the backend API without
/// constructing lifecycle state directly.
pub(crate) fn test_compile_program_and_run(
    program: &[TopLevel],
    check: &TestCheckResult,
    tables: &DashMap<ModuleFullPath, SymbolTable>,
) -> Result<i64, CranelispError> {
    let module = ModuleFullPath::from("user");

    // Enrich and collect all TopLevel::Defn entries from the program,
    // plus default_method_defns and mono specialisations from the check
    // (historically injected into the program by finalize_module).
    let mut defns: Vec<Defn> = Vec::new();
    for tl in program {
        if let TopLevel::Defn(defn) = tl {
            let mut d = defn.clone();
            enrich_defn_from_side_maps(&mut d, &check.method_resolutions, &check.expr_types);
            defns.push(d);
        }
    }
    for d in &check.default_method_defns {
        let mut enriched = d.clone();
        enrich_defn_from_side_maps(&mut enriched, &check.method_resolutions, &check.expr_types);
        defns.push(enriched);
    }
    for mono in &check.mono_defns {
        // FIXME 0033 (resolved S81): `MonoDefn` no longer carries
        // `resolutions`/`expr_types` side maps — its `defn` AST is already
        // annotated by typecheck's `monomorphise_call`. Overlay only the
        // global test side maps (a no-op where the AST is already
        // annotated; keeps legacy scaffolding that pre-populates the
        // global maps working).
        let mut enriched = mono.defn.clone();
        enrich_defn_from_side_maps(&mut enriched, &check.method_resolutions, &check.expr_types);
        defns.push(enriched);
    }

    // Install ordinary defns. Multi-signature fixtures are installed by their
    // tests as one already-checked owned family, matching the production
    // typecheck boundary.
    let mut targets: Vec<CallableTarget> = Vec::new();
    let mut entry_name = None;
    {
        let mut st = tables
            .entry(module.clone())
            .or_insert_with(|| SymbolTable::new(module.clone()));
        for defn in defns {
            if defn.is_multi_sig() {
                let owner = defn.name.clone();
                targets.extend(st.codegen_targets().filter_map(|(target, _)| {
                    matches!(
                        &target,
                        CallableTarget::OverloadArm { owner: fq, .. }
                            if fq.module == module && fq.symbol == owner
                    )
                    .then_some(target)
                }));
            } else {
                let name = defn.name.clone();
                if defn
                    .variants
                    .first()
                    .is_some_and(|variant| variant.params.is_empty())
                {
                    entry_name = Some(name.clone());
                }
                install_def_entry_with_targets(&mut st, defn, &check.resolved_targets);
                targets.push(binding_target(&module, &name));
            }
        }
    }

    let mut jit = Jit::new(tables)?;
    let _artifacts = compile_to_module(module.clone(), &targets, tables, jit.jit_module(), true)?;
    // `compile_to_module` finalizes the JIT internally. Each concrete fixture
    // owns a lifecycle-minted slot; the executed entry is the last zero-arg
    // defn and is invoked directly by its finalized JIT symbol.
    let entry_name = entry_name.ok_or_else(|| CranelispError::CodegenError {
        message: "no entry function (no zero-arg defn)".into(),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })?;
    let ptr = jit.get_ptr_by_name(&entry_name, 0)?;
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    let value = func();
    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        return Err(CranelispError::CodegenError {
            message: format!("runtime panic: {}", msg),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }
    Ok(value)
}

/// Build symbol tables with an Option type for ADT tests.
pub(crate) fn option_type_tables() -> DashMap<ModuleFullPath, SymbolTable> {
    use cranelisp_types::{
        Binding, CallableOrigin, ConcreteType, Decl, FQTypeName, MonoDefnVariant, MonoExpr,
        Realization, Scheme, Type, TypeDefInfo, TypeName, TypeRecord, Visibility,
    };

    let module = ModuleFullPath::from("main");
    let type_name = TypeName::from("Option");
    let fqtn = FQTypeName::new(module.clone(), type_name.clone());

    // Constructors are now Def entries; TypeDefInfo carries names only.
    let type_def_info = TypeDefInfo {
        name: fqtn.clone(),
        type_params: vec![],
        constructors: vec![Symbol::from("None"), Symbol::from("Some")],
    };

    let tables = DashMap::new();
    let mut st = SymbolTable::new(module.clone());

    // Insert type def
    st.install_binding(
        Symbol::from("Option"),
        Binding::new(
            Decl::Type(TypeRecord::Defined {
                info: type_def_info.clone(),
                docstring: None,
            }),
            Visibility::Public,
        ),
    )
    .expect("install Option type fixture");

    let mut install_ctor = |name: &str, tag: usize, field_count: usize, scheme_ty: Type| {
        let name = Symbol::from(name);
        st.install_concrete(
            name.clone(),
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: scheme_ty,
            },
            (0..field_count)
                .map(|i| Symbol::from(format!("f{i}")))
                .collect(),
            None,
            tag as u64,
            CallableOrigin::Ctor {
                type_name: fqtn.clone(),
                tag,
                field_count,
                internal: false,
                type_def: None,
            },
            Realization::Body {
                view: MonoDefnVariant {
                    name,
                    params: vec![],
                    body: MonoExpr::IntLit {
                        value: tag as i64,
                        span: Span::SYNTHETIC,
                        ty: ConcreteType::Int,
                    },
                    span: Span::SYNTHETIC,
                    mode_summary: None,
                },
                code: None,
            },
            None,
            vec![],
            Visibility::Public,
        )
        .expect("install constructor fixture");
    };

    // None: nullary; scheme is the bare ADT.
    install_ctor("None", 0, 0, Type::ADT(fqtn.clone(), vec![]));

    // Some: one Int field; scheme is Int -> Option.
    install_ctor(
        "Some",
        1,
        1,
        Type::Fn(vec![Type::Int], Box::new(Type::ADT(fqtn.clone(), vec![]))),
    );

    tables.insert(module, st);
    tables
}

// ----- Sprint 58 Wave 2: Decision 36 + Decision 23 unit tests -----
//
// These tests cover the architectural reconciliation landed in Sprint 58
// Wave 2: bare-name + Linkage::Local function declarations uniformly across
// all modules (Decision 36), and `__cranelisp_got_{M}` defined as
// Linkage::Export data symbol in the .o (Decision 23 — Bug B fix).

/// Helper: make an ObjectModule for these tests (PIC enabled).
pub(crate) fn make_object_module() -> cranelift_object::ObjectModule {
    use cranelift_module::default_libcall_names;
    use cranelift_object::ObjectBuilder;

    let isa = crate::cache::object::build_isa(true).unwrap();
    let builder = ObjectBuilder::new(isa, "test", default_libcall_names()).unwrap();
    cranelift_object::ObjectModule::new(builder)
}

/// Helper: build a single-defn symbol table with `got_slot: Some(slot)` so
/// the GOT-data emission step has a slot to populate.
pub(crate) fn table_with_def_and_slot(
    module: &ModuleFullPath,
    defn: Defn,
    slot: usize,
) -> DashMap<ModuleFullPath, SymbolTable> {
    let tables = DashMap::new();
    let mut st = SymbolTable::new(module.clone());
    install_def_entry_at_slot(&mut st, defn, slot);
    tables.insert(module.clone(), st);
    tables
}

/// Helper: trivial zero-arg defn returning an int literal.
pub(crate) fn make_int_defn(name: &str, value: i64) -> Defn {
    Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value,
                span: Span::SYNTHETIC,
                inferred_type: None,
            },
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

// =========================================================================
// Vec query family (vec-get/vec-set/vec-push/vec-len) as first-class
// values must inline-emit in the generated wrapper, never call through a GOT
// slot. Post S102 FIXME-0476 (change-set B1-be), these entries use
// `Life::Inline` — no slot at all, so "resolvable but not slot-callable" is a
// lifecycle state, not an allocated-but-NULL slot (Principle 20).
// (`design/backend/ownership-codegen.md` §12.7/§13.2; e2e guards:
// `tests/vec_query_value_use.rs`.)
// =========================================================================

/// Install a slotless inline Vec primitive. Value-use wrappers receive the
/// concrete element type at the reference site, not from a shared extern body.
pub(crate) fn insert_inline_vec_query_entry(
    st: &mut SymbolTable,
    name: &str,
    param_names: &[&str],
    ty: Type,
) {
    use cranelisp_types::Scheme;
    let scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty,
    };
    st.install_inline(
        Symbol::from(name),
        scheme,
        param_names.iter().map(|s| Symbol::from(*s)).collect(),
        None,
        0,
        None,
        Visibility::Public,
    )
    .expect("install inline primitive fixture");
}

/// Read element `idx` from a Vec base pointer (layout per Decision 11:
/// `[size@+0 | rc@+8 | len@+16 | cap@+24 | data_ptr@+32]`). Test-only inline
/// (Decision 0048 backend dep-ban — no `cranelisp-primitives` dep).
///
/// SAFETY: `ptr` must be a valid Vec base pointer with `idx < len`.
pub(crate) fn vec_elem_for_test(ptr: i64, idx: usize) -> i64 {
    unsafe {
        let data_ptr = *((ptr as *const u8).add(32) as *const *const i64);
        *data_ptr.add(idx)
    }
}

/// Shared fixture driver for the vec-query fn-as-value seam: builds a
/// `primitives` table holding slotless inline Vec-query
/// entries and a `user` module with the given consumer defn, compiles the
/// consumer, and runs it end-to-end. Returns the consumer's i64 result.
pub(crate) fn run_vec_query_value_consumer(consumer: Defn) -> i64 {
    let user = ModuleFullPath::from("user");
    let prims = ModuleFullPath::from("primitives");
    let vec_int = || {
        Type::adt(
            ModuleFullPath::from("primitives"),
            cranelisp_types::TypeName::from("Vec"),
            vec![Type::Int],
        )
    };

    let tables = empty_tables();
    {
        let mut pst = SymbolTable::new(prims.clone());
        insert_inline_vec_query_entry(
            &mut pst,
            "vec-len",
            &["v"],
            Type::Fn(vec![vec_int()], Box::new(Type::Int)),
        );
        insert_inline_vec_query_entry(
            &mut pst,
            "vec-get",
            &["v", "idx"],
            Type::Fn(vec![vec_int(), Type::Int], Box::new(Type::Int)),
        );
        insert_inline_vec_query_entry(
            &mut pst,
            "vec-set",
            &["v", "idx", "val"],
            Type::Fn(vec![vec_int(), Type::Int, Type::Int], Box::new(vec_int())),
        );
        insert_inline_vec_query_entry(
            &mut pst,
            "vec-push",
            &["v", "val"],
            Type::Fn(vec![vec_int(), Type::Int], Box::new(vec_int())),
        );
        tables.insert(prims.clone(), pst);
    }
    let consumer_name = consumer.name.clone();
    {
        // S110 W2 (KC-K8): the value-position vec-query primitive `Var`
        // (`(let [f vec-get] …)`) reads its carrier at the fn-as-value gate /
        // vec-query discrimination — populate it with `{primitives, <prim>}`, the
        // storage FQ the producer records for such a value ref.
        let mut resolved_targets = HashMap::new();
        for variant in &consumer.variants {
            collect_vec_query_value_carriers(&variant.body, &mut resolved_targets);
        }
        let mut st = SymbolTable::new(user.clone());
        install_def_entry_at_slot_with_targets(&mut st, consumer.clone(), 0, &resolved_targets);
        tables.insert(user.clone(), st);
    }

    // Register both GOT data symbols. The user slab backs the consumer's own
    // slot write; the primitives slab is what the DEFECTIVE path GOT-indirects
    // through (registering it makes the RED failure the production SIGSEGV,
    // not an unresolved-symbol artifact).
    let got_user_name = crate::compiler::got_data_symbol_name(&user);
    let got_prims_name = crate::compiler::got_data_symbol_name(&prims);
    let (got_user_base, got_prims_base) = (
        tables
            .get(&user)
            .map(|st| st.got.base_ptr())
            .expect("user table"),
        tables
            .get(&prims)
            .map(|st| st.got.base_ptr())
            .expect("prims table"),
    );
    let extras: Vec<(&str, *const u8)> = vec![
        (got_user_name.as_str(), got_user_base),
        (got_prims_name.as_str(), got_prims_base),
    ];

    let mut jit = Jit::new_with_symbols(&extras).expect("jit init");
    compile_names_to_module(
        user.clone(),
        std::slice::from_ref(&consumer_name),
        &tables,
        jit.jit_module(),
        true,
    )
    .expect("vec-query value-use consumer must compile");

    let ptr = jit
        .get_ptr_by_name(&consumer_name, 0)
        .expect("finalize consumer");
    assert!(
        !ptr.is_null(),
        "consumer must finalize to a non-null fn ptr"
    );
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    let result = func();
    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        panic!("runtime panic running vec-query consumer: {msg}");
    }
    result
}

/// Fully-annotated `(Vec Int)` literal `[e0 e1 ...]` fixture node.
pub(crate) fn vec_int_lit(elements: &[i64], span_base: u32) -> Expr {
    let vec_int = Type::adt(
        ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
        vec![Type::Int],
    );
    Expr::VecLit {
        elements: elements
            .iter()
            .enumerate()
            .map(|(i, &v)| Expr::IntLit {
                value: v,
                span: Span::new(span_base + i as u32, span_base + i as u32 + 1),
                inferred_type: Some(Box::new(Type::Int)),
            })
            .collect(),
        span: Span::new(span_base, span_base + elements.len() as u32 + 1),
        inferred_type: Some(Box::new(vec_int)),
    }
}

/// `(let [f <prim>] (f <args...>))` consumer fixture: the vec-query primitive
/// referenced as a VALUE (resolved_call: None — the fn-as-value fall-through
/// in `compile_var`), then applied through the local closure binding.
pub(crate) fn vec_query_value_consumer(
    prim: &str,
    prim_ty: Type,
    args: Vec<Expr>,
    result_ty: Type,
) -> Defn {
    let body = Expr::Let {
        bindings: vec![(
            Symbol::from("f"),
            Expr::Var {
                name: Symbol::from(prim),
                span: Span::new(10, 17),
                resolved_call: None,
                inferred_type: Some(Box::new(prim_ty.clone())),
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("f"),
                span: Span::new(20, 21),
                resolved_call: None,
                inferred_type: Some(Box::new(prim_ty)),
            }),
            args,
            span: Span::new(19, 60),
            resolved_call: None,
            inferred_type: Some(Box::new(result_ty.clone())),
        }),
        span: Span::new(5, 61),
        inferred_type: Some(Box::new(result_ty)),
    };
    Defn {
        name: Symbol::from("use-vec-query"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::new(0, 62),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 62),
    }
}

/// A standalone canonical drop-glue registry for unit fixtures that build an
/// inner [`crate::compiler::FnCompiler`] directly (S118 slice S0). Production
/// owns exactly one registry per `compile_to_module`; a fixture that constructs
/// a compiler by hand owns one for the fixture's duration.
pub(crate) fn probe_glue_registry(
    module_path: ModuleFullPath,
    intrinsic_ids: &crate::jit::IntrinsicFuncIds,
) -> crate::drop_glue::DropGlueRegistry {
    crate::drop_glue::DropGlueRegistry::new(
        module_path,
        intrinsic_ids
            .dealloc
            .expect("probe: runtime/dealloc declared"),
        intrinsic_ids.vec_drop,
    )
}

/// Count the RELEASE operations a rendered CLIF body performs on its own heap
/// values (S118 slice S6 — the shared counting instrument for the RC fence
/// cells).
///
/// After the consumer migration a release takes one of two forms, and a cell
/// that watches only one of them silently stops measuring:
///
/// - a `call` to a **canonical drop glue** — the release ABI `(i64) -> ()`, one
///   heap word in and nothing out, so its signature is unmistakable in the CLIF
///   preamble (`sigN = (i64) system_v`); this is now every scope-exit, match and
///   capture release;
/// - an **inline** `atomic_rmw.i64 sub` — the remaining per-site RC decs
///   (`heap::emit_rc_dec*`, the Vec-op temporary release) that are not type
///   glue.
///
/// The sum is "how many times does this body release something", which is the
/// question every 0781/0782-class fence actually asks.
pub(crate) fn count_release_ops(clif: &str) -> usize {
    let release_sigs: Vec<&str> = clif
        .lines()
        .filter_map(|l| {
            let l = l.trim();
            let (name, rest) = l.split_once(" = ")?;
            (name.starts_with("sig") && rest == "(i64) system_v").then_some(name)
        })
        .collect();
    let release_fns: Vec<&str> = clif
        .lines()
        .filter_map(|l| {
            let l = l.trim();
            let (name, rest) = l.split_once(" = ")?;
            let sig = rest.rsplit(' ').next()?;
            (name.starts_with("fn") && release_sigs.contains(&sig)).then_some(name)
        })
        .collect();
    let glue_calls = clif
        .lines()
        .filter(|l| {
            release_fns
                .iter()
                .any(|f| l.contains(&format!("call {f}(")))
        })
        .count();
    glue_calls + clif.matches("atomic_rmw.i64 sub").count()
}

/// Compile `(defn f [p0 ..] body)` in module `user` against `tables` and return
/// its CLIF. `params` spells each parameter's type and `result` the return
/// type; `carriers` are the span-keyed dispatch carriers the body's references
/// need (for a primitive, `{primitives, name}` on the `Apply` and callee spans).
pub(crate) fn probe_caller_clif(
    tables: &DashMap<ModuleFullPath, SymbolTable>,
    carriers: &HashMap<Span, cranelisp_types::FQSymbol>,
    params: &[Type],
    result: Type,
    body: Expr,
) -> String {
    let user = ModuleFullPath::from("user");
    let defn = Defn {
        name: Symbol::from("f"),
        docstring: None,
        variants: vec![DefnVariant {
            params: (0..params.len())
                .map(|i| (Symbol::from(format!("p{i}")), None))
                .collect(),
            body,
            span: Span::new(0, 1000),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 1000),
    };
    insert_user_fn_stub_typed(
        &mut tables
            .entry(user.clone())
            .or_insert_with(|| SymbolTable::new(user.clone())),
        "f",
        params,
        result,
    );
    let mut jit = Jit::new_with_symbols(&[]).expect("jit");
    try_compile_defns_in_module(&[&defn], &[], &[], carriers, tables, user, jit.jit_module())
        .expect("probe: f compiles")
        .into_iter()
        .next()
        .expect("probe: one compiled defn")
}

/// Fixtures for the §13.7 COW-site cells (`design/backend/ownership-codegen.md`
/// §13.5 "COW cores" and "Match scrutinee plan" rows): a `defn` over owned
/// `Vec Int` parameters in module `main`, compiled through the production
/// per-body seam, whose COW sites carry one chosen escape fact.
pub(crate) mod cow_site_fixture {
    use std::sync::atomic::{AtomicU32, Ordering};

    use cranelisp_types::{
        Defn, DefnVariant, Expr, FQTypeName, MatchArm, Mode, ModeSummary, ModuleFullPath, MonoExpr,
        Pattern, ResolvedCall, Span, Symbol, Type, Visibility,
    };

    static NEXT_SPAN: AtomicU32 = AtomicU32::new(50_000);

    /// A span no other node shares: last-use facts are keyed by span.
    fn span() -> Span {
        let start = NEXT_SPAN.fetch_add(2, Ordering::Relaxed);
        Span::new(start, start + 1)
    }

    pub(crate) fn vec_ty() -> Type {
        Type::ADT(
            FQTypeName::new("primitives".into(), "Vec".into()),
            vec![Type::Int],
        )
    }

    fn var(name: &str, ty: &Type) -> Expr {
        Expr::Var {
            name: Symbol::from(name),
            span: span(),
            resolved_call: None,
            inferred_type: Some(Box::new(ty.clone())),
        }
    }

    pub(crate) fn vec_var(name: &str) -> Expr {
        var(name, &vec_ty())
    }

    pub(crate) fn int(value: i64) -> Expr {
        Expr::IntLit {
            value,
            span: span(),
            inferred_type: Some(Box::new(Type::Int)),
        }
    }

    /// `[]`, a fresh `Vec Int`.
    pub(crate) fn empty_vec() -> Expr {
        Expr::VecLit {
            elements: vec![],
            span: span(),
            inferred_type: Some(Box::new(vec_ty())),
        }
    }

    /// `(op args…)` resolved to the inline Vec builtin `op`.
    fn vec_op(op: &str, args: Vec<Expr>) -> Expr {
        let result = if op == "vec-len" { Type::Int } else { vec_ty() };
        Expr::Apply {
            callee: Box::new(var(op, &Type::Int)),
            args,
            span: span(),
            resolved_call: Some(Box::new(ResolvedCall::BuiltinFn { name: op.into() })),
            inferred_type: Some(Box::new(result)),
        }
    }

    /// `(vec-set source 0 5)`.
    pub(crate) fn vec_set(source: Expr) -> Expr {
        vec_op("vec-set", vec![source, int(0), int(5)])
    }

    /// `(vec-push source value)`.
    pub(crate) fn vec_push(source: Expr, value: i64) -> Expr {
        vec_push_of(source, int(value))
    }

    /// `(vec-push source value)` with a computed element.
    pub(crate) fn vec_push_of(source: Expr, value: Expr) -> Expr {
        vec_op("vec-push", vec![source, value])
    }

    pub(crate) fn vec_len(source: Expr) -> Expr {
        vec_op("vec-len", vec![source])
    }

    pub(crate) fn let_in(bindings: Vec<(&str, Expr)>, body: Expr, ty: Type) -> Expr {
        Expr::Let {
            bindings: bindings
                .into_iter()
                .map(|(name, value)| (Symbol::from(name), value))
                .collect(),
            body: Box::new(body),
            span: span(),
            inferred_type: Some(Box::new(ty)),
        }
    }

    /// `(match scrutinee [binder body])`.
    pub(crate) fn match_var(scrutinee: Expr, binder: &str, body: Expr, ty: Type) -> Expr {
        let pattern = Pattern::Var {
            name: Symbol::from(binder),
            span: span(),
        };
        match_one_arm(scrutinee, pattern, body, ty)
    }

    /// `(match scrutinee [_ body])`.
    pub(crate) fn match_wildcard(scrutinee: Expr, body: Expr, ty: Type) -> Expr {
        match_one_arm(scrutinee, Pattern::Wildcard { span: span() }, body, ty)
    }

    fn match_one_arm(scrutinee: Expr, pattern: Pattern, body: Expr, ty: Type) -> Expr {
        Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![MatchArm {
                pattern,
                body,
                span: span(),
            }],
            span: span(),
            compiler_generated: false,
            inferred_type: Some(Box::new(ty)),
        }
    }

    /// Set `escapes` on every COW-builtin site of the shapes built above.
    fn set_cow_escapes(node: &mut MonoExpr, escapes: Option<bool>) {
        if crate::compiler::vec_codegen::cow_site_source(node).is_some()
            && let MonoExpr::Apply { escapes: fact, .. } = node
        {
            *fact = escapes;
        }
        match node {
            MonoExpr::Apply { args, .. } => {
                args.iter_mut().for_each(|a| set_cow_escapes(a, escapes));
            }
            MonoExpr::Let { bindings, body, .. } => {
                for (_, value) in bindings.iter_mut() {
                    set_cow_escapes(value, escapes);
                }
                set_cow_escapes(body, escapes);
            }
            MonoExpr::Match {
                scrutinee, arms, ..
            } => {
                set_cow_escapes(scrutinee, escapes);
                for arm in arms.iter_mut() {
                    set_cow_escapes(&mut arm.body, escapes);
                }
            }
            _ => {}
        }
    }

    /// Compile `(defn f [params…] body)`, every parameter an `Owned` `Vec Int`
    /// and every COW site carrying `escapes`, and return its CLIF.
    pub(crate) fn compile_f(
        params: &[&str],
        body: Expr,
        result: Type,
        escapes: Option<bool>,
    ) -> String {
        let main = ModuleFullPath::from("main");
        let defn = Defn {
            name: Symbol::from("f"),
            docstring: None,
            variants: vec![DefnVariant {
                params: params.iter().map(|p| (Symbol::from(*p), None)).collect(),
                body,
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let tables = super::option_type_tables();
        super::insert_user_fn_stub_typed(
            &mut tables.get_mut(&main).expect("main table"),
            "f",
            &vec![vec_ty(); params.len()],
            result,
        );
        let summary = ModeSummary {
            param_modes: vec![Mode::Owned; params.len()],
            ..ModeSummary::default()
        };
        let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("JIT construction");
        super::try_compile_defns_in_module_with_pattern_ctors(
            &[&defn],
            &[Some(summary)],
            &[],
            &super::HashMap::new(),
            &super::HashMap::new(),
            &tables,
            main,
            jit.jit_module(),
            &|body| set_cow_escapes(body, escapes),
        )
        .unwrap_or_else(|e| panic!("compile f: {e}"))
        .pop()
        .expect("one compiled defn")
    }

    /// Inline increments. With `Int` elements and RC stats off, the only
    /// increments these shapes can emit are a reused box's retention and a
    /// return protect.
    pub(crate) fn increments(clif: &str) -> usize {
        clif.matches("atomic_rmw.i64 add").count()
    }

    /// Every release: canonical glue calls and inline decrements.
    pub(crate) fn releases(clif: &str) -> usize {
        super::count_release_ops(clif)
    }
}
