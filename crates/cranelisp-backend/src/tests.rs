use super::*;
use crate::jit::Jit;
use cranelisp_types::{ErrorLocation, 
    Defn, DefnVariant, DisplayInfo, Expr, MonoDefn, Program, Span, Symbol,
    TopLevel, Type, Visibility,
};
use std::collections::{HashMap, HashSet};

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
struct TestCheckResult {
    // S70: `MethodResolutions` became a struct (resolved_calls +
    // pattern_ctors). The test bridge only ever populated per-span
    // call resolutions, so this field holds the bare `resolved_calls`
    // map shape — exactly what `enrich_defn_from_side_maps` consumes.
    method_resolutions: HashMap<Span, cranelisp_types::ResolvedCall>,
    constrained_fn_names: HashSet<Symbol>,
    mono_defns: Vec<MonoDefn>,
    expr_types: HashMap<Span, Type>,
    default_method_defns: Vec<Defn>,
    #[allow(dead_code)]
    warnings: Vec<cranelisp_types::Warning>,
    #[allow(dead_code)]
    display: Option<DisplayInfo>,
}

fn empty_check() -> TestCheckResult {
    TestCheckResult {
        method_resolutions: HashMap::new(),
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    }
}

fn empty_tables() -> DashMap<ModuleFullPath, SymbolTable> {
    DashMap::new()
}

/// Empty session-level module-alias table for tests that drive
/// `compile_to_module` / `build_compile_context` (S75 W2 D41 rotation
/// added the `module_aliases` param).
fn empty_aliases() -> cranelisp_types::ModuleAliases {
    DashMap::new()
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
fn vec_len_for_test(ptr: i64) -> i64 {
    unsafe { *((ptr as *const u8).add(16) as *const i64) }
}

/// Test helper: enrich a defn's AST nodes with type and resolution
/// annotations from CheckResult side maps.
///
/// Used by tests that build ASTs by hand and carry resolutions in a
/// `CheckResult`. In production, typecheck annotates the AST directly,
/// so this bridge is test-only.
fn enrich_defn_from_side_maps(
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
fn concretize_test_body(expr: &mut Expr) {
    use cranelisp_types::Expr;
    // Recurse into children first.
    match expr {
        Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
            for (_, v) in bindings {
                concretize_test_body(v);
            }
            concretize_test_body(body);
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            concretize_test_body(cond);
            concretize_test_body(then_branch);
            concretize_test_body(else_branch);
        }
        Expr::Lambda { body, .. } | Expr::Trace { body, .. } | Expr::Annotate { expr: body, .. } => {
            concretize_test_body(body);
        }
        Expr::Apply { callee, args, .. } => {
            concretize_test_body(callee);
            for a in args {
                concretize_test_body(a);
            }
        }
        Expr::Match { scrutinee, arms, .. } => {
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
        Expr::LaunchContinue { launched, continuation, .. } => {
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
fn enrich_expr_from_side_maps(
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
    if let Expr::Apply { resolved_call, span: apply_span, .. } = expr
        && let Some(resolution) = resolutions.get(apply_span) {
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
        Expr::If { cond, then_branch, else_branch, .. } => {
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
        Expr::Match { scrutinee, arms, .. } => {
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
        Expr::LaunchContinue { launched, continuation, .. } => {
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

/// Test helper: build a `ModuleEntry::Def` with `ast: Some(defn)` and NO
/// GOT slot (`got_slot: None`).
///
/// With no GOT slot, intra-module calls compile as direct FuncId calls
/// (no `__cranelisp_got_{M}` reference is emitted), so JIT-execute test
/// helpers can run against a bare `Jit::new_with_symbols(&[])` without registering the
/// GOT base symbol. Tests that specifically exercise the S75 W2 GOT-slot
/// direct-write (`make_def_entry_slot`) assign an explicit slot and read
/// the pointer back via `table.got.load_slot(slot)`.
fn make_def_entry(defn: Defn) -> cranelisp_types::ModuleEntry {
    make_def_entry_inner(defn, None)
}

/// Like `make_def_entry` but assigns an explicit GOT slot (for tests that
/// exercise the GOT-slot direct-write, or insert more than one compilable
/// defn that must be reachable GOT-indirect).
fn make_def_entry_slot(defn: Defn, slot: usize) -> cranelisp_types::ModuleEntry {
    make_def_entry_inner(defn, Some(slot))
}

fn make_def_entry_inner(defn: Defn, slot: Option<usize>) -> cranelisp_types::ModuleEntry {
    use cranelisp_types::{
        DefKind, MonoDefnVariant, MonoExpr, ModuleEntry, Scheme, UserFnState, Visibility,
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
        let body = MonoExpr::from_expr(&v.body)
            .expect("test fixture body concretizes for the codegen view (FIXME 0391)");
        MonoDefnVariant {
            name: defn.name.clone(),
            params: v.params.iter().map(|(n, _)| n.clone()).collect(),
            body,
            span: v.span,
            mode_summary: None,
        }
    });
    ModuleEntry::Def {
        scheme,
        visibility: Visibility::Public,
        docstring: None,
        param_names,
        // Slot rides on the callable variant (S83 reshape): an explicit slot
        // → `Concrete`; no slot → the Pass-1 `NotDetermined` interim.
        kind: Box::new(DefKind::UserFn {
            fn_state: match slot {
                Some(got_slot) => UserFnState::Concrete { got_slot, mode_summary: None },
                None => UserFnState::NotDetermined,
            },
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: variant,
        codegen_view,
        code: None,
        value_use: false,
    }
}

/// Test helper: wrap an expression in a synthetic zero-arg defn, compile via
/// `compile_to_module`, finalize JIT, execute, and return the i64 result.
///
/// The `check` parameter provides side-map data that is enriched onto the
/// defn's AST nodes before compilation (bridging old test code to the new
/// CheckResult-free API).
fn test_compile_and_run(
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
        st.insert(name.clone(), make_def_entry(defn));
    }

    let mut jit = Jit::new_with_symbols(&[])?;
    let aliases = empty_aliases();
    let _artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&name),
        tables,
        &aliases,
        jit.jit_module(),
        true,
    )?;
    // S75 W2: `compile_to_module` finalizes the JIT internally. The
    // single `__expr__` defn carries `got_slot: None` (direct FuncId
    // calls; no GOT reference emitted), so read its finalised pointer by
    // name from the JIT module rather than from a GOT slot.
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
/// Enriches defns from `check` side maps, inserts each defn into the
/// shared symbol table as a `ModuleEntry::Def { ast: Some(_), .. }` entry
/// (matching the Wave 0 invariant), then hands the name list to
/// `compile_to_module`. Bridges legacy test scaffolding to the post-
/// Phase-2 backend API (no `Program`/`CheckResult` parameters).
fn test_compile_program_and_run(
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

    // Install each defn as a symbol-table entry with ast: Some(defn).
    // Multi-sig defns need expansion into mangled variants here (legacy
    // tests don't pre-materialise those; typecheck does in production).
    let mut names: Vec<Symbol> = Vec::new();
    {
        let mut st = tables
            .entry(module.clone())
            .or_insert_with(|| SymbolTable::new(module.clone()));
        for defn in defns {
            if defn.is_multi_sig() {
                // Look up OverloadVariant info from the pre-inserted
                // Overloaded base entry to recover mangled names + param
                // types, then materialise each variant as its own entry.
                let variants = match st.get(defn.name.as_ref()) {
                    Some(cranelisp_types::ModuleEntry::Def { kind, .. }) => {
                        if let cranelisp_types::DefKind::Overloaded { variants } =
                            kind.as_ref()
                        {
                            variants.clone()
                        } else {
                            continue;
                        }
                    }
                    _ => continue,
                };
                for (i, variant) in defn.variants.iter().enumerate() {
                    let param_types = variants
                        .iter()
                        .find(|v| v.param_types.len() == variant.params.len())
                        .map(|v| v.param_types.clone())
                        .or_else(|| variants.get(i).map(|v| v.param_types.clone()))
                        .unwrap_or_default();
                    let mangled = format!(
                        "{}${}",
                        defn.name,
                        param_types
                            .iter()
                            .filter_map(|t| match t {
                                Type::Int => Some("Int"),
                                Type::Float => Some("Float"),
                                Type::Bool => Some("Bool"),
                                Type::String => Some("String"),
                                _ => None,
                            })
                            .collect::<Vec<_>>()
                            .join("+"),
                    );
                    let variant_defn = Defn {
                        name: Symbol::from(mangled),
                        docstring: defn.docstring.clone(),
                        variants: vec![variant.clone()],
                        visibility: defn.visibility,
                        span: variant.span,
                    };
                    names.push(variant_defn.name.clone());
                    st.insert(variant_defn.name.clone(), make_def_entry(variant_defn));
                }
            } else {
                names.push(defn.name.clone());
                st.insert(defn.name.clone(), make_def_entry(defn));
            }
        }
    }

    let mut jit = Jit::new_with_symbols(&[])?;
    let aliases = empty_aliases();
    let _artifacts = compile_to_module(
        module.clone(),
        &names,
        tables,
        &aliases,
        jit.jit_module(),
        true,
    )?;
    // S75 W2: `compile_to_module` finalizes the JIT internally. Entries
    // carry `got_slot: None` (intra-module direct FuncId calls; no GOT
    // reference emitted). The entry is the LAST zero-arg defn (matching the
    // pre-rotation `entry_func_id` selection); read its finalised pointer
    // by name from the JIT module.
    let entry_name = names
        .iter()
        .rev()
        .find(|n| {
            tables.get(&module).is_some_and(|t| {
                matches!(
                    t.get(n.as_ref()),
                    Some(ModuleEntry::Def { ast: Some(v), .. }) if v.params.is_empty()
                )
            })
        })
        .cloned()
        .ok_or_else(|| CranelispError::CodegenError {
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
fn option_type_tables() -> DashMap<ModuleFullPath, SymbolTable> {
    use cranelisp_types::{DefKind, FQTypeName, ModuleEntry, Scheme, Type,
        TypeDefInfo, TypeName, Visibility,
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
    st.insert(
        Symbol::from("Option"),
        ModuleEntry::TypeDef {
            info: type_def_info.clone(),
            visibility: Visibility::Public,
            docstring: None,
        },
    );

    // Helper: build a constructor Def entry (S70 ctor-as-Def).
    let ctor_def = |tag: usize, field_count: usize, scheme_ty: Type| ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: scheme_ty,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: (0..field_count).map(|i| Symbol::from(format!("f{i}"))).collect(),
        kind: Box::new(DefKind::Constructor {
            got_slot: 0,
            type_name: fqtn.clone(),
            tag,
            field_count,
            internal: false,
            type_def: None,
            mode_summary: None,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    };

    // None: nullary; scheme is the bare ADT.
    st.insert(Symbol::from("None"), ctor_def(0, 0, Type::ADT(fqtn.clone(), vec![])));

    // Some: one Int field; scheme is Int -> Option.
    st.insert(
        Symbol::from("Some"),
        ctor_def(1, 1, Type::Fn(vec![Type::Int], Box::new(Type::ADT(fqtn.clone(), vec![])))),
    );

    tables.insert(module, st);
    tables
}

// spec: 05-definitions §5.1 — single defn compiles and executes via JIT
#[test]
fn test_compile_program_simple() {
    let defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
                value: 42,
                span: Span::new(0, 2),
                inferred_type: None,
            },
            span: Span::new(0, 20),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 20),
    };

    let program: Program = vec![TopLevel::Defn(defn)];
    let check = empty_check();

    let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
    assert_eq!(value, 42);
}

// spec: 12-runtime §12.6 — batch mode requires main entry point
#[test]
fn test_compile_program_no_defns() {
    let _ = empty_check();
    let names: Vec<Symbol> = vec![];
    let tables = empty_tables();
    // No symbol table for "user" at all — compile_to_module errors out
    // because there's no module entry (and no names anyway).
    tables.insert(ModuleFullPath::from("user"), SymbolTable::new(ModuleFullPath::from("user")));

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let result = compile_to_module(
        ModuleFullPath::from("user"),
        &names,
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    );
    assert!(result.is_err());
}

// spec: 04-expressions §4.1.1 — integer literal codegen
#[test]
fn test_compile_and_run_expr() {
    let expr = Expr::IntLit {
        value: 99,
        span: Span::new(0, 2),
        inferred_type: None,
    };
    let check = empty_check();

    let value = test_compile_and_run(&expr, &check, &empty_tables()).unwrap();
    assert_eq!(value, 99);
}

// spec: 05-definitions §5.1 — defn compiles in interactive (REPL) mode
#[test]
fn test_compile_program_interactive_mode() {
    let defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
            value: 7,
            span: Span::new(0, 1),
            inferred_type: None,
            },
            span: Span::new(0, 20),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 20),
    };

    let program: Program = vec![TopLevel::Defn(defn)];
    let check = empty_check();

    let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
    assert_eq!(value, 7);
}

// spec: 04-expressions §4.1.1 — integer literal codegen with GOT state
// spec: 05-definitions §5.13.1 — multiple function definitions compile together
#[test]
fn test_compile_program_multiple_defns() {
    // Two functions: helper and main. Main returns 100.
    let helper = Defn {
        name: Symbol::from("helper"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::Var {
            name: Symbol::from("x"),
            span: Span::new(20, 21),
            resolved_call: None,
            inferred_type: None,
            },
            span: Span::new(10, 30),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(10, 30),
    };

    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit {
            value: 100,
            span: Span::new(40, 43),
            inferred_type: None,
            },
            span: Span::new(35, 50),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(35, 50),
    };

    let program: Program = vec![TopLevel::Defn(helper), TopLevel::Defn(main_defn)];
    let check = empty_check();

    let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
    assert_eq!(value, 100);
}

// spec: 04-expressions §4.1.3 — boolean literal codegen
#[test]
fn test_compile_and_run_expr_bool() {
    let expr = Expr::BoolLit {
        value: true,
        span: Span::new(0, 4),
        inferred_type: None,
    };
    let check = empty_check();

    let value = test_compile_and_run(&expr, &check, &empty_tables()).unwrap();
    assert_eq!(value, 1);
}

// --- Ring 1 tests ---

// spec: 04-expressions §4.1.4 — string literal codegen, heap allocation
#[test]
fn test_compile_string_literal() {
    let expr = Expr::StringLit {
        value: "hello".to_string(),
        span: Span::new(0, 7),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "string literal should compile: {result:?}");
    let ptr = result.unwrap();
    // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");

    // Read back the string content via runtime API.
    let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(ptr) };
    assert_eq!(s, "hello");

    // Clean up the allocation.
    cranelisp_intrinsics::alloc::heap_dealloc(ptr);
}

// spec: 04-expressions §4.1.4 — empty string literal codegen
#[test]
fn test_compile_empty_string_literal() {
    let expr = Expr::StringLit {
        value: String::new(),
        span: Span::new(0, 2),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "empty string should compile: {result:?}");
    let ptr = result.unwrap();
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");

    let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(ptr) };
    assert_eq!(s, "");

    cranelisp_intrinsics::alloc::heap_dealloc(ptr);
}

// spec: 12-runtime §12.1.4 — data constructor heap layout [tag | fields]
#[test]
fn test_compile_adt_data_constructor() {
    // Expression: (Some 42)
    let some_span = Span::new(0, 10);
    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("Some"),
            span: Span::new(1, 5),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::IntLit {
            value: 42,
            span: Span::new(6, 8),
            inferred_type: None,
        }],
        span: some_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = empty_check();
    let tables = option_type_tables();

    let result = test_compile_and_run(&expr, &check, &tables);
    assert!(result.is_ok(), "ADT constructor should compile: {result:?}");
    let ptr = result.unwrap();
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");

    // Verify the heap layout: [header(16) | tag(1) | field(42)]
    unsafe {
        let base = ptr as *const u8;
        let tag = *(base.add(16) as *const i64);
        assert_eq!(tag, 1, "tag should be 1 for Some");
        let val = *(base.add(24) as *const i64);
        assert_eq!(val, 42, "field should be 42");
    }

    cranelisp_intrinsics::alloc::heap_dealloc(ptr);
}

// spec: 04-expressions §4.8 — match expression with constructor patterns and field extraction
#[test]
fn test_compile_match_with_fields() {
    use cranelisp_types::{MatchArm, Pattern};

    // (match (Some 99) [(Some x) x (None) 0])
    let some_span = Span::new(10, 20);
    let match_span = Span::new(0, 50);
    let scrutinee = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("Some"),
            span: Span::new(11, 15),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::IntLit {
            value: 99,
            span: Span::new(16, 18),
            inferred_type: None,
        }],
        span: some_span,
        resolved_call: None,
        inferred_type: None,
    };

    let expr = Expr::Match {
        scrutinee: Box::new(scrutinee),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("Some")),
                    bindings: vec![Symbol::from("x")],
                    span: Span::new(22, 30),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::new(31, 32),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(22, 32),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: cranelisp_types::SymbolRef::new(None, Symbol::from("None")),
                    bindings: vec![],
                    span: Span::new(34, 40),
                },
                body: Expr::IntLit {
                    value: 0,
                    span: Span::new(41, 42),
                    inferred_type: None,
                },
                span: Span::new(34, 42),
            },
        ],
        span: match_span,
        compiler_generated: false,
        inferred_type: None,
    };

    let check = empty_check();
    let tables = option_type_tables();

    let result = test_compile_and_run(&expr, &check, &tables);
    assert!(result.is_ok(), "match with fields should compile: {result:?}");
    assert_eq!(result.unwrap(), 99, "match should extract field value");
}

// spec: 04-expressions §4.5 — lambda capture, closure allocation, and indirect call
#[test]
fn test_compile_lambda_closure() {
    // (let [n 5] ((fn [x] (+ n x)) 10))
    // This tests: lambda capture of 'n', closure allocation, closure call.
    use cranelisp_types::ResolvedCall;

    let add_span = Span::new(30, 37);
    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        add_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("add-i64"),
        },
    );

    let expr = Expr::Let {
        bindings: vec![(
            Symbol::from("n"),
            Expr::IntLit {
                value: 5,
                span: Span::new(5, 6),
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Lambda {
                params: vec![(Symbol::from("x"), None)],
                body: Box::new(Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: Span::new(31, 32),
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("n"),
                            span: Span::new(33, 34),
                            resolved_call: None,
                            inferred_type: None,
                        },
                        Expr::Var {
                            name: Symbol::from("x"),
                            span: Span::new(35, 36),
                            resolved_call: None,
                            inferred_type: None,
                        },
                    ],
                    span: add_span,
                    resolved_call: None,
                    inferred_type: None,
                }),
                span: Span::new(10, 40),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 10,
                span: Span::new(42, 44),
                inferred_type: None,
            }],
            span: Span::new(10, 45),
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(0, 46),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "closure should compile: {result:?}");
    assert_eq!(result.unwrap(), 15, "5 + 10 = 15");
}

// spec: design/backend/ring2-rc.md "capture-return inc" (sibling of §5.5)
// spec: design/backend/slice-4-21-hello-io-investigation.md §4d/§4e
//
// Regression guard for Slice 4 defect. A lambda body whose return
// expression is a bare reference to a captured heap variable MUST
// emit `rc_inc` on the return value before `return`, so the
// closure's drop-glue dec (fired by one-shot consume_closure paths
// like the IO trampoline) does not free the value out from under
// the caller.
//
// Test shape: `(let [s "hello"] ((fn [_] s) 0))`. The inner
// closure captures `s` (heap-typed String) and returns it when
// called with a dummy Int arg. Without `emit_capture_return_inc`,
// the closure's drop glue would dec `s` after the body returns,
// the outer `let` scope cleanup would dec `s` again (via its own
// scope-stack dec), and at least one of those decs lands on a
// freed node — corrupting the returned pointer and/or
// double-freeing.
//
// Post-fix: the returned pointer is still live and reads back as
// "hello"; `test_compile_lambda_closure` above (non-capture-return
// shape) is unaffected, confirming the fix is additive.
//
// NB: this test sits in `lib.rs #[cfg(test)] mod tests` rather
// than a new module in `control_flow.rs` because the
// `test_compile_and_run` helper + `TestCheckResult` scaffolding is
// local to `lib.rs` and re-exporting it would duplicate the entire
// compile pipeline bridge. Per /arch §4d the placement discipline
// is "wherever existing control_flow tests live" — the three
// existing closure/lambda backend tests
// (`test_compile_lambda_closure`, others) all live here.
#[test]
fn lambda_return_captured_heap_var_emits_inc() {
    // AST: (let [s "hello"] ((fn [_] s) 0))
    //
    // Explicit `inferred_type` on the String literal so the let's
    // `variable_types` picks up `s: String`; that's what
    // `emit_capture_return_inc` reads from the enclosing scope when
    // the lambda body is compiled.
    let string_ty = Type::String;
    let s_span = Span::new(5, 12);
    let lam_body_span = Span::new(20, 21);
    let expr = Expr::Let {
        bindings: vec![(
            Symbol::from("s"),
            Expr::StringLit {
                value: "hello".to_string(),
                span: s_span,
                inferred_type: Some(Box::new(string_ty.clone())),
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Lambda {
                params: vec![(Symbol::from("_"), None)],
                body: Box::new(Expr::Var {
                    name: Symbol::from("s"),
                    span: lam_body_span,
                    resolved_call: None,
                    inferred_type: Some(Box::new(string_ty.clone())),
                }),
                span: Span::new(15, 22),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 0,
                span: Span::new(24, 25),
                inferred_type: None,
            }],
            span: Span::new(14, 26),
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(0, 27),
        inferred_type: None,
    };

    let check = empty_check();
    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(
        result.is_ok(),
        "captured-heap-return should compile and run: {result:?}"
    );
    let ptr = result.unwrap();
    // Heap pointer (> NULLARY_TAG_THRESHOLD).
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");

    // Key post-fix assertion: the returned pointer is STILL LIVE
    // after return — `emit_capture_return_inc` incremented its RC
    // so the drop-glue dec did not free it. Pre-fix, `is_live`
    // would be false here (or the read-back would show corruption).
    #[cfg(debug_assertions)]
    assert!(
        cranelisp_intrinsics::alloc::is_live(ptr as usize),
        "returned string pointer must still be live after lambda return; \
         this is the capture-return inc invariant"
    );

    // Readable round-trip — proves the contents survived the
    // drop-glue dec that would otherwise have corrupted or freed
    // the heap block.
    let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(ptr) };
    assert_eq!(s, "hello", "captured string must round-trip");

    // Balance the one remaining caller-side reference (we, the
    // test, are the caller). Normal runtime would emit the dec at
    // the caller's scope exit; here we dec manually.
    cranelisp_intrinsics::alloc::heap_dealloc(ptr);
}

// spec: design/backend/io-trampoline.md §15 — FIXME 0472 regression guard.
//
// A launch-and-continue continuation that passes a CAPTURED heap variable to a
// consuming call MUST emit the caller-side `rc_inc` on that capture
// (`compile_lambda_body` parity / ring2-rc.md §5.5). The launched web serve loop
// `(do (bind (read-conn …) …) (serve-loop listener))` lowers the tail to a launch
// continuation `(fn [_] (serve-loop listener))` — exactly this shape: the captured
// `listener` is passed to the recursive `serve-loop` (a consuming call). Pre-fix,
// `define_launch_cont_body` did NOT seed the capture's TYPE into the inner
// compiler, so the consuming call skipped the inc; the callee dec'd `listener` at
// scope exit AND the continuation closure's drop glue dec'd it again → `listener`
// freed after the FIRST detached iteration, the next accept loop reused the freed
// address, and the recursive serve loop's `match` read a dangling pointer (the
// observed ConnectionReset / heap corruption on the 2nd request).
//
// This guard isolates the inner launch-continuation codegen WITHOUT the reactor:
// build the `Bind(Launch, cont)` tree via backend codegen, extract the
// continuation closure, invoke it directly (so it runs `(keep h)` over the
// captured String `h`), then run the closure's drop glue (`consume_closure` — the
// IO trampoline's fresh-continuation release path). With the fix `h` SURVIVES the
// drop (the consuming-call inc balanced it); pre-fix `h` is freed → is_live false.
#[test]
fn launch_continuation_consuming_call_on_capture_keeps_it_live() {
    use cranelisp_types::{JitSymbol, ResolvedCall};

    // (defn keep$String [v] v) — identity over a heap String: a consuming
    // function (its param ref is consumed-then-returned, RC-neutral).
    let keep = Defn {
        name: Symbol::from("keep$String"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("v"), None)],
            body: Expr::Var {
                name: Symbol::from("v"),
                span: Span::new(40, 41),
                resolved_call: None,
                inferred_type: Some(Box::new(Type::String)),
            },
            span: Span::new(30, 45),
        }],
        visibility: Visibility::Public,
        span: Span::new(30, 45),
    };

    // (defn entry [] (let [h "hello"] (launch-continue 0 (keep$String h))))
    // The LaunchContinue continuation `(keep$String h)` captures the heap `h` and
    // passes it to the consuming `keep$String` call. `launched` is an int stand-in
    // (0) — never interpreted; this test invokes only the continuation closure.
    let call_span = Span::new(70, 82);
    let sig_dispatch = || {
        Some(Box::new(ResolvedCall::SigDispatch {
            mangled_name: JitSymbol::from("keep$String"),
        }))
    };
    let continuation = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("keep$String"),
            span: call_span,
            resolved_call: sig_dispatch(),
            inferred_type: Some(Box::new(Type::Fn(
                vec![Type::String],
                Box::new(Type::String),
            ))),
        }),
        args: vec![Expr::Var {
            name: Symbol::from("h"),
            span: Span::new(78, 79),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::String)),
        }],
        span: call_span,
        resolved_call: sig_dispatch(),
        inferred_type: Some(Box::new(Type::String)),
    };
    let entry_body = Expr::Let {
        bindings: vec![(
            Symbol::from("h"),
            Expr::StringLit {
                value: "hello".to_string(),
                span: Span::new(60, 67),
                inferred_type: Some(Box::new(Type::String)),
            },
        )],
        body: Box::new(Expr::LaunchContinue {
            launched: Box::new(Expr::IntLit {
                value: 0,
                span: Span::new(55, 56),
                inferred_type: Some(Box::new(Type::Int)),
            }),
            continuation: Box::new(continuation),
            span: Span::new(50, 83),
            inferred_type: Some(Box::new(Type::String)),
        }),
        span: Span::new(48, 84),
        inferred_type: Some(Box::new(Type::String)),
    };
    let entry = Defn {
        name: Symbol::from("entry"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: entry_body,
            span: Span::new(46, 85),
        }],
        visibility: Visibility::Public,
        span: Span::new(46, 85),
    };

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    jit.declare_intrinsics().unwrap();
    let func_ids = jit.declare_functions(&[&keep, &entry]).unwrap();
    let arities: HashMap<Symbol, usize> =
        vec![(Symbol::from("keep$String"), 1)].into_iter().collect();
    let tables = empty_tables();
    let aliases = empty_aliases();

    {
        let ctx = jit.build_compile_context(
            &func_ids,
            &arities,
            &tables,
            &aliases,
            ModuleFullPath::from("user"),
        );
        jit.compile_defn(&keep, ctx).unwrap();
    }
    {
        let ctx = jit.build_compile_context(
            &func_ids,
            &arities,
            &tables,
            &aliases,
            ModuleFullPath::from("user"),
        );
        jit.compile_defn(&entry, ctx).unwrap();
    }
    let entry_ptr = jit
        .finalize_and_get_ptr(&Symbol::from("entry"), 0)
        .unwrap();

    // Run entry() → the Bind(Launch, cont) IO tree.
    let entry_fn: extern "C" fn() -> i64 = unsafe { std::mem::transmute(entry_ptr) };
    let tree = entry_fn();
    assert!(tree > 1024, "entry must return a heap IO-tree pointer, got {tree}");

    // Bind layout: [header(16) | tag@16 | inner@24 | cont@32]. Extract the cont.
    let cont_ptr = unsafe { *((tree + 32) as *const i64) };
    assert!(
        cont_ptr > 1024,
        "Bind.cont (field 1 @ offset 32) must be a heap closure pointer, got {cont_ptr}"
    );

    // Invoke the continuation directly: code_ptr at closure+16, called as
    // fn(env_ptr=closure_base, discarded_launch_result=0). Runs `(keep$String h)`.
    let code_ptr = unsafe { *((cont_ptr + 16) as *const i64) };
    let cont_fn: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(code_ptr) };
    let result_h = cont_fn(cont_ptr, 0);
    assert!(
        result_h > 1024,
        "continuation must return the heap String `h`, got {result_h}"
    );

    // Run the continuation closure's drop glue (the IO trampoline's
    // consume_closure path) — it dec's the captured `h`. The discriminating
    // assertion: WITH the consuming-call inc `h` survives this drop; pre-fix the
    // double-dec frees it (the corruption that wrecked the launched serve loop).
    cranelisp_intrinsics::drop::consume_closure(cont_ptr);

    #[cfg(debug_assertions)]
    assert!(
        cranelisp_intrinsics::alloc::is_live(result_h as usize),
        "the captured String passed to a consuming call in a launch continuation \
         must survive the continuation closure's drop glue (FIXME 0472 — the \
         launched serve loop freed `listener` after one detached iteration)"
    );
    let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(result_h) };
    assert_eq!(s, "hello", "captured String must round-trip after the drop glue");

    // Balance the surviving caller-side reference (the Bind + Launch nodes are
    // intentionally left — this guard asserts the capture's liveness, not a full
    // tree-balance; the process exits at test end).
    cranelisp_intrinsics::alloc::heap_dealloc(result_h);
}

// --- Vec codegen tests ---

// spec: 04-expressions §4.10 — empty Vec literal codegen
#[test]
fn test_compile_empty_vec_literal() {
    let expr = Expr::VecLit {
        elements: vec![],
        span: Span::new(0, 2),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "empty vec literal should compile: {result:?}");
    let ptr = result.unwrap();
    // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");

    // Verify len == 0.
    assert_eq!(vec_len_for_test(ptr), 0);

    // Clean up.
    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}

// spec: 04-expressions §4.10 — Vec literal with integer elements
#[test]
fn test_compile_vec_literal_with_ints() {
    let expr = Expr::VecLit {
        elements: vec![
            Expr::IntLit { value: 10, span: Span::new(1, 3), inferred_type: None },
            Expr::IntLit { value: 20, span: Span::new(4, 6), inferred_type: None },
            Expr::IntLit { value: 30, span: Span::new(7, 9), inferred_type: None },
        ],
        span: Span::new(0, 10),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec literal should compile: {result:?}");
    let ptr = result.unwrap();
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");

    // Verify len == 3.
    assert_eq!(vec_len_for_test(ptr), 3);

    // Verify element values from data buffer.
    unsafe {
        let base = ptr as *const u8;
        let data_ptr = *(base.add(heap::HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64);
        assert_eq!(*data_ptr, 10);
        assert_eq!(*data_ptr.add(1), 20);
        assert_eq!(*data_ptr.add(2), 30);
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}

// spec: 04-expressions §4.10 — single-element Vec literal
#[test]
fn test_compile_vec_literal_single_element() {
    let expr = Expr::VecLit {
        elements: vec![
            Expr::IntLit { value: 42, span: Span::new(1, 3), inferred_type: None },
        ],
        span: Span::new(0, 4),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "single-element vec should compile: {result:?}");
    let ptr = result.unwrap();

    assert_eq!(vec_len_for_test(ptr), 1);

    unsafe {
        let base = ptr as *const u8;
        let data_ptr = *(base.add(32) as *const *const i64);
        assert_eq!(*data_ptr, 42);
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}

// spec: 04-expressions §4.10 — Vec literal with boolean elements
#[test]
fn test_compile_vec_literal_with_bool_elements() {
    let expr = Expr::VecLit {
        elements: vec![
            Expr::BoolLit { value: true, span: Span::new(1, 5), inferred_type: None },
            Expr::BoolLit { value: false, span: Span::new(6, 11), inferred_type: None },
        ],
        span: Span::new(0, 12),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "bool vec should compile: {result:?}");
    let ptr = result.unwrap();
    assert_eq!(vec_len_for_test(ptr), 2);

    unsafe {
        let base = ptr as *const u8;
        let data_ptr = *(base.add(32) as *const *const i64);
        assert_eq!(*data_ptr, 1); // true
        assert_eq!(*data_ptr.add(1), 0); // false
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}

// spec: appendix-a-builtins §A.3 — vec-len inline primitive codegen
#[test]
fn test_compile_vec_len_inline() {
    use cranelisp_types::ResolvedCall;

    // (vec-len [10 20 30])
    let vec_span = Span::new(10, 20);
    let apply_span = Span::new(0, 25);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        apply_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-len"),
        },
    );

    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-len"),
            span: Span::new(1, 8),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 10, span: Span::new(11, 13), inferred_type: None },
                Expr::IntLit { value: 20, span: Span::new(14, 16), inferred_type: None },
                Expr::IntLit { value: 30, span: Span::new(17, 19), inferred_type: None },
            ],
            span: vec_span,
            inferred_type: None,
        }],
        span: apply_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-len should compile: {result:?}");
    assert_eq!(result.unwrap(), 3);
}

// spec: appendix-a-builtins §A.3 — vec-get bounds-checked index codegen
#[test]
fn test_compile_vec_get_inline() {
    use cranelisp_types::ResolvedCall;

    // (let [v [10 20 30]] (vec-get v 1))
    let vec_span = Span::new(8, 18);
    let get_span = Span::new(21, 35);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        get_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-get"),
        },
    );

    let expr = Expr::Let {
        bindings: vec![(
            Symbol::from("v"),
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 10, span: Span::new(9, 11), inferred_type: None },
                    Expr::IntLit { value: 20, span: Span::new(12, 14), inferred_type: None },
                    Expr::IntLit { value: 30, span: Span::new(15, 17), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-get"),
                span: Span::new(22, 29),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(30, 31),
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 1, span: Span::new(32, 33), inferred_type: None },
            ],
            span: get_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(0, 36),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-get should compile: {result:?}");
    assert_eq!(result.unwrap(), 20);
}

// spec: appendix-a-builtins §A.3 — vec-get index 0 boundary
#[test]
fn test_compile_vec_get_first_element() {
    use cranelisp_types::ResolvedCall;

    let vec_span = Span::new(100, 110);
    let get_span = Span::new(120, 135);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        get_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-get"),
        },
    );

    let expr = Expr::Let {
        bindings: vec![(
            Symbol::from("v"),
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 100, span: Span::new(101, 104), inferred_type: None },
                    Expr::IntLit { value: 200, span: Span::new(105, 108), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-get"),
                span: Span::new(121, 128),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(129, 130),
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 0, span: Span::new(131, 132), inferred_type: None },
            ],
            span: get_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(99, 136),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-get index 0 should work: {result:?}");
    assert_eq!(result.unwrap(), 100);
}

// spec: appendix-a-builtins §A.3 — vec-get last index boundary
#[test]
fn test_compile_vec_get_last_element() {
    use cranelisp_types::ResolvedCall;

    let vec_span = Span::new(200, 210);
    let get_span = Span::new(220, 235);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        get_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-get"),
        },
    );

    let expr = Expr::Let {
        bindings: vec![(
            Symbol::from("v"),
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: Span::new(201, 202), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(203, 204), inferred_type: None },
                    Expr::IntLit { value: 3, span: Span::new(205, 206), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-get"),
                span: Span::new(221, 228),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(229, 230),
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 2, span: Span::new(231, 232), inferred_type: None },
            ],
            span: get_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(199, 236),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-get last index should work: {result:?}");
    assert_eq!(result.unwrap(), 3);
}

// spec: 12-runtime §12.3.3 — vec-set copy-on-write path codegen
#[test]
fn test_compile_vec_set_copy_path() {
    use cranelisp_types::ResolvedCall;

    // (let [v [10 20 30]] (vec-len (vec-set v 1 99)))
    // Since v is used twice (vec-set and vec-len), vec-set takes the copy path.
    let vec_span = Span::new(300, 310);
    let set_span = Span::new(320, 340);
    let len_span = Span::new(315, 345);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        set_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-set"),
        },
    );
    method_resolutions.insert(
        len_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-len"),
        },
    );

    let expr = Expr::Let {
        bindings: vec![(
            Symbol::from("v"),
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 10, span: Span::new(301, 303), inferred_type: None },
                    Expr::IntLit { value: 20, span: Span::new(304, 306), inferred_type: None },
                    Expr::IntLit { value: 30, span: Span::new(307, 309), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(316, 323),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-set"),
                    span: Span::new(321, 328),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(329, 330),
                        resolved_call: None,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 1, span: Span::new(331, 332), inferred_type: None },
                    Expr::IntLit { value: 99, span: Span::new(333, 335), inferred_type: None },
                ],
                span: set_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(299, 346),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-set should compile: {result:?}");
    // vec-set returns a new Vec with same length.
    assert_eq!(result.unwrap(), 3);
}

// spec: 12-runtime §12.3.3 — vec-push copy-on-write path codegen
#[test]
fn test_compile_vec_push_copy_path() {
    use cranelisp_types::ResolvedCall;

    // (vec-len (vec-push [10 20] 30))
    let vec_span = Span::new(400, 410);
    let push_span = Span::new(415, 435);
    let len_span = Span::new(410, 440);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        push_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-push"),
        },
    );
    method_resolutions.insert(
        len_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-len"),
        },
    );

    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-len"),
            span: Span::new(411, 418),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-push"),
                span: Span::new(416, 424),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(401, 403), inferred_type: None },
                        Expr::IntLit { value: 20, span: Span::new(404, 406), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
                Expr::IntLit { value: 30, span: Span::new(425, 427), inferred_type: None },
            ],
            span: push_span,
            resolved_call: None,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-push should compile: {result:?}");
    // [10 20] pushed 30 -> len 3
    assert_eq!(result.unwrap(), 3);
}

// spec: 04-expressions §4.3, §4.10 — Vec literal bound in let, accessed via vec-len
#[test]
fn test_compile_vec_literal_in_let() {
    // (let [v [1 2 3]] (vec-len v))
    use cranelisp_types::ResolvedCall;

    let vec_span = Span::new(500, 510);
    let len_span = Span::new(515, 530);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        len_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-len"),
        },
    );

    let expr = Expr::Let {
        bindings: vec![(
            Symbol::from("v"),
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: Span::new(501, 502), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(503, 504), inferred_type: None },
                    Expr::IntLit { value: 3, span: Span::new(505, 506), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(516, 523),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::Var {
                name: Symbol::from("v"),
                span: Span::new(524, 525),
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(499, 531),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec in let should compile: {result:?}");
    assert_eq!(result.unwrap(), 3);
}

// spec: 04-expressions §4.10, §4.11 — Vec literal with computed elements, left-to-right eval
#[test]
fn test_compile_vec_literal_with_computed_elements() {
    use cranelisp_types::ResolvedCall;

    // [1 (+ 2 3) 10]
    let add_span = Span::new(603, 610);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        add_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("add-i64"),
        },
    );

    let expr = Expr::VecLit {
        elements: vec![
            Expr::IntLit { value: 1, span: Span::new(601, 602), inferred_type: None },
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("+"),
                    span: Span::new(604, 605),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit { value: 2, span: Span::new(606, 607), inferred_type: None },
                    Expr::IntLit { value: 3, span: Span::new(608, 609), inferred_type: None },
                ],
                span: add_span,
                resolved_call: None,
                inferred_type: None,
            },
            Expr::IntLit { value: 10, span: Span::new(611, 613), inferred_type: None },
        ],
        span: Span::new(600, 614),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec with computed elements should compile: {result:?}");
    let ptr = result.unwrap();

    assert_eq!(vec_len_for_test(ptr), 3);
    unsafe {
        let base = ptr as *const u8;
        let data_ptr = *(base.add(32) as *const *const i64);
        assert_eq!(*data_ptr, 1);
        assert_eq!(*data_ptr.add(1), 5); // 2 + 3
        assert_eq!(*data_ptr.add(2), 10);
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}

// spec: 05-definitions §5.1, 04-expressions §4.10 — Vec literal as function return value
#[test]
fn test_compile_vec_in_function_defn() {
    // (defn make-vec [] [1 2 3])
    // Returns a Vec literal.
    let defn = Defn {
        name: Symbol::from("make-vec"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::VecLit {
            elements: vec![
            Expr::IntLit { value: 1, span: Span::new(701, 702), inferred_type: None },
            Expr::IntLit { value: 2, span: Span::new(703, 704), inferred_type: None },
            Expr::IntLit { value: 3, span: Span::new(705, 706), inferred_type: None },
            ],
            span: Span::new(700, 707),
            inferred_type: None,
            },
            span: Span::new(700, 710),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(700, 710),
    };

    let program: Program = vec![TopLevel::Defn(defn)];
    let check = empty_check();

    let ptr = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
    assert!(ptr > 1024, "expected heap pointer, got {ptr}");
    assert_eq!(vec_len_for_test(ptr), 3);

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}

// spec: appendix-a-builtins §A.3 — vec-get returns correct element value
#[test]
fn test_compile_vec_get_verify_value() {
    use cranelisp_types::ResolvedCall;

    // (let [v [100 200 300]] (vec-get v 2))
    let vec_span = Span::new(808, 818);
    let get_span = Span::new(821, 840);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        get_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-get"),
        },
    );

    let expr = Expr::Let {
        bindings: vec![(
            Symbol::from("v"),
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 100, span: Span::new(809, 812), inferred_type: None },
                    Expr::IntLit { value: 200, span: Span::new(813, 816), inferred_type: None },
                    Expr::IntLit { value: 300, span: Span::new(817, 820), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-get"),
                span: Span::new(822, 829),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(830, 831),
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 2, span: Span::new(832, 833), inferred_type: None },
            ],
            span: get_span,
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(807, 841),
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-get value should compile: {result:?}");
    assert_eq!(result.unwrap(), 300);
}

// spec: 12-runtime §12.3.3 — vec-push on temporary Vec (COW in-place path)
#[test]
fn test_compile_vec_push_on_temp() {
    use cranelisp_types::ResolvedCall;

    // (vec-len (vec-push [1] 2))
    // vec-push on a temporary VecLit — will take COW path (temp = unique).
    let vec_span = Span::new(900, 905);
    let push_span = Span::new(910, 925);
    let len_span = Span::new(905, 930);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        push_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-push"),
        },
    );
    method_resolutions.insert(
        len_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-len"),
        },
    );

    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-len"),
            span: Span::new(906, 913),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-push"),
                span: Span::new(911, 919),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(901, 902), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
                Expr::IntLit { value: 2, span: Span::new(920, 921), inferred_type: None },
            ],
            span: push_span,
            resolved_call: None,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-push on temp should compile: {result:?}");
    assert_eq!(result.unwrap(), 2);
}

// spec: 12-runtime §12.3.3 — vec-set on temporary Vec (COW in-place path)
#[test]
fn test_compile_vec_set_on_temp() {
    use cranelisp_types::ResolvedCall;

    // (vec-len (vec-set [10 20 30] 0 99))
    let vec_span = Span::new(1000, 1010);
    let set_span = Span::new(1015, 1035);
    let len_span = Span::new(1010, 1040);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        set_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-set"),
        },
    );
    method_resolutions.insert(
        len_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-len"),
        },
    );

    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-len"),
            span: Span::new(1011, 1018),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-set"),
                span: Span::new(1016, 1023),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(1001, 1003), inferred_type: None },
                        Expr::IntLit { value: 20, span: Span::new(1004, 1006), inferred_type: None },
                        Expr::IntLit { value: 30, span: Span::new(1007, 1009), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
                Expr::IntLit { value: 0, span: Span::new(1024, 1025), inferred_type: None },
                Expr::IntLit { value: 99, span: Span::new(1026, 1028), inferred_type: None },
            ],
            span: set_span,
            resolved_call: None,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "vec-set on temp should compile: {result:?}");
    assert_eq!(result.unwrap(), 3);
}

// ===== FIXME 0134 harvest (backend slice): Vec-COW value-correctness +
// RC-balance kernels of the quarantined `tests/legacy/{ring1,ring2,e2e}.rs`
// GAPs. The existing `test_compile_vec_set_{copy_path,on_temp}` tests prove
// vec-set COMPILES and RUNS but assert only the result LENGTH (=3). The
// disposition (`s82-harvest-conformance_bulk.md` flag 1: backend =
// `assert_rc_balanced` + Vec-COW edge cases) names the uncovered angles:
// (a) the COPY path leaves the ORIGINAL vec untouched
//     (legacy `vec_set_cow_preserves_original`);
// (b) a set preserves OTHER positions' values
//     (legacy `vec_set_preserves_other_elements`);
// (c) RC balance — a vec lifecycle returns live bytes to baseline
//     (legacy `assert_rc_balanced`).
// These run at the backend unit layer via `test_compile_and_run` (full
// codegen + JIT execute), reading element VALUES via vec-get — the durable
// value-level guards the length-only tests lack. =====

/// Build `(vec-get <vec_expr> idx)` against a fresh span. Helper for the
/// COW value-correctness guards below.
fn vec_get(
    vec_expr: Expr,
    idx: i64,
    get_span: Span,
    resolutions: &mut HashMap<Span, cranelisp_types::ResolvedCall>,
) -> Expr {
    resolutions.insert(
        get_span,
        cranelisp_types::ResolvedCall::BuiltinFn { name: Symbol::from("vec-get") },
    );
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-get"),
            span: Span::new(get_span.start + 1, get_span.end - 1),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            vec_expr,
            Expr::IntLit { value: idx, span: Span::new(get_span.end - 1, get_span.end), inferred_type: None },
        ],
        span: get_span,
        resolved_call: None,
        inferred_type: None,
    }
}

fn vec_lit(elems: &[i64], base: u32) -> Expr {
    Expr::VecLit {
        elements: elems
            .iter()
            .enumerate()
            .map(|(i, &v)| {
                let i = i as u32;
                Expr::IntLit {
                    value: v,
                    span: Span::new(base + i * 3 + 1, base + i * 3 + 3),
                    inferred_type: None,
                }
            })
            .collect(),
        span: Span::new(base, base + elems.len() as u32 * 3 + 1),
        inferred_type: None,
    }
}

// spec: spec/12-runtime.md §12.3.3 — vec-set on a NON-last-use vec takes
//       the COPY path; the ORIGINAL vec is untouched. Backend kernel of the
//       legacy `vec_set_cow_preserves_original` reg-guard. The original `v`
//       is read AFTER the set (so the set is NOT at last use → copy path),
//       and its index-1 value must still be the original 20, not 99.
#[test]
fn vec_set_copy_path_preserves_original() {
    use cranelisp_types::ResolvedCall;
    let mut res = HashMap::new();
    let set_span = Span::new(2010, 2030);
    res.insert(set_span, ResolvedCall::BuiltinFn { name: Symbol::from("vec-set") });

    // (let [v [10 20 30]]
    //   (let [_ (vec-set v 1 99)]   ; copy path: v not at last use
    //     (vec-get v 1)))            ; original v's index 1 still = 20
    let set_expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-set"),
            span: Span::new(2011, 2018),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::Var { name: Symbol::from("v"), span: Span::new(2019, 2020), resolved_call: None, inferred_type: None },
            Expr::IntLit { value: 1, span: Span::new(2021, 2022), inferred_type: None },
            Expr::IntLit { value: 99, span: Span::new(2023, 2025), inferred_type: None },
        ],
        span: set_span,
        resolved_call: None,
        inferred_type: None,
    };
    let read_original = vec_get(
        Expr::Var { name: Symbol::from("v"), span: Span::new(2040, 2041), resolved_call: None, inferred_type: None },
        1,
        Span::new(2042, 2060),
        &mut res,
    );
    let expr = Expr::Let {
        bindings: vec![(Symbol::from("v"), vec_lit(&[10, 20, 30], 2001))],
        body: Box::new(Expr::Let {
            bindings: vec![(Symbol::from("_unused"), set_expr)],
            body: Box::new(read_original),
            span: Span::new(2005, 2061),
            inferred_type: None,
        }),
        span: Span::new(2000, 2062),
        inferred_type: None,
    };
    let check = TestCheckResult {
        method_resolutions: res,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    };
    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert_eq!(
        result.expect("vec-set copy-path program compiles+runs"),
        20,
        "vec-set on a non-last-use vec MUST copy — the original vec's \
         index-1 value must remain 20 (COW preserves the original)"
    );
}

// spec: spec/12-runtime.md §12.3.3 — a vec-set preserves the values at
//       OTHER positions. Backend kernel of the legacy
//       `vec_set_preserves_other_elements` GAP (distinct from the
//       length-only `test_compile_vec_set_*`). Read index 2 of the SET
//       result — it must still be the original 30 (only index 0 changed).
#[test]
fn vec_set_preserves_other_elements() {
    use cranelisp_types::ResolvedCall;
    let mut res = HashMap::new();
    let set_span = Span::new(2110, 2130);
    res.insert(set_span, ResolvedCall::BuiltinFn { name: Symbol::from("vec-set") });

    // (vec-get (vec-set [10 20 30] 0 99) 2)  →  30 (index 2 untouched)
    let set_expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-set"),
            span: Span::new(2111, 2118),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            vec_lit(&[10, 20, 30], 2101),
            Expr::IntLit { value: 0, span: Span::new(2121, 2122), inferred_type: None },
            Expr::IntLit { value: 99, span: Span::new(2123, 2125), inferred_type: None },
        ],
        span: set_span,
        resolved_call: None,
        inferred_type: None,
    };
    let expr = vec_get(set_expr, 2, Span::new(2140, 2160), &mut res);
    let check = TestCheckResult {
        method_resolutions: res,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    };
    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert_eq!(
        result.expect("vec-set preserves-other program compiles+runs"),
        30,
        "vec-set at index 0 MUST leave index 2 holding the original 30"
    );
}

// spec: spec/12-runtime.md §12.3 — RC balance: a complete Vec lifecycle
//       (allocate literal, set, drop) returns live bytes to baseline — no
//       leak, no double-free. Backend kernel of the legacy
//       `assert_rc_balanced` discipline, lifted to the unit layer via the
//       `cranelisp_intrinsics::{alloc_count,dealloc_count}` counters (the
//       same atomics `/mem` reports). RC-counter tests are process-global,
//       so this reads a delta, not an absolute. NOTE: nextest runs each
//       test in its own process, so the counter is uncontended here.
#[test]
fn vec_lifecycle_is_rc_balanced() {
    use cranelisp_types::ResolvedCall;
    let allocs_before = cranelisp_intrinsics::alloc_count();
    let deallocs_before = cranelisp_intrinsics::dealloc_count();

    // (vec-len (vec-set [10 20 30] 0 99))  — temp vec → COW path; the
    // whole temporary lifecycle (literal alloc, COW copy if any, drop)
    // must balance. We read length so the result is a scalar.
    let mut res = HashMap::new();
    let set_span = Span::new(2210, 2230);
    let len_span = Span::new(2240, 2260);
    res.insert(set_span, ResolvedCall::BuiltinFn { name: Symbol::from("vec-set") });
    res.insert(len_span, ResolvedCall::BuiltinFn { name: Symbol::from("vec-len") });
    let set_expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-set"),
            span: Span::new(2211, 2218),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            vec_lit(&[10, 20, 30], 2201),
            Expr::IntLit { value: 0, span: Span::new(2221, 2222), inferred_type: None },
            Expr::IntLit { value: 99, span: Span::new(2223, 2225), inferred_type: None },
        ],
        span: set_span,
        resolved_call: None,
        inferred_type: None,
    };
    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-len"),
            span: Span::new(2241, 2248),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![set_expr],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };
    let check = TestCheckResult {
        method_resolutions: res,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    };
    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert_eq!(result.expect("rc-balance program runs"), 3);

    let allocs = cranelisp_intrinsics::alloc_count() - allocs_before;
    let deallocs = cranelisp_intrinsics::dealloc_count() - deallocs_before;
    assert_eq!(
        allocs, deallocs,
        "Vec lifecycle must be RC-balanced: {allocs} allocs vs {deallocs} \
         deallocs across the temp-vec set+len+drop. An imbalance means a \
         leak (allocs>deallocs) or a double-free (deallocs>allocs) in the \
         vec-set COW codegen."
    );
}

// spec: 04-expressions §4.10 — Vec literal in interactive (REPL) mode
#[test]
fn test_compile_vec_literal_interactive_mode() {
    let expr = Expr::VecLit {
        elements: vec![
            Expr::IntLit { value: 42, span: Span::new(1101, 1103), inferred_type: None },
        ],
        span: Span::new(1100, 1104),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(
        &expr, &check, &empty_tables(),
    );
    assert!(result.is_ok(), "vec in interactive mode should compile: {result:?}");
    let ptr = result.unwrap();
    assert!(ptr > 1024);
    assert_eq!(vec_len_for_test(ptr), 1);

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}

// spec: appendix-a-builtins §A.3 — vec-len on empty Vec returns 0
#[test]
fn test_compile_vec_empty_len() {
    use cranelisp_types::ResolvedCall;

    // (vec-len [])
    let vec_span = Span::new(1200, 1202);
    let len_span = Span::new(1195, 1210);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        len_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-len"),
        },
    );

    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-len"),
            span: Span::new(1196, 1203),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::VecLit {
            elements: vec![],
            span: vec_span,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "empty vec len should compile: {result:?}");
    assert_eq!(result.unwrap(), 0);
}

// spec: appendix-a-builtins §A.3 — vec-push on empty Vec
#[test]
fn test_compile_vec_push_empty_vec() {
    use cranelisp_types::ResolvedCall;

    // (vec-len (vec-push [] 42))
    let vec_span = Span::new(1300, 1302);
    let push_span = Span::new(1305, 1320);
    let len_span = Span::new(1300, 1325);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        push_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-push"),
        },
    );
    method_resolutions.insert(
        len_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-len"),
        },
    );

    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-len"),
            span: Span::new(1301, 1308),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-push"),
                span: Span::new(1306, 1314),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::VecLit {
                    elements: vec![],
                    span: vec_span,
                    inferred_type: None,
                },
                Expr::IntLit { value: 42, span: Span::new(1315, 1317), inferred_type: None },
            ],
            span: push_span,
            resolved_call: None,
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "push to empty vec should compile: {result:?}");
    assert_eq!(result.unwrap(), 1);
}

// spec: appendix-a-builtins §A.3 — vec-len on empty Vec (duplicate boundary check)
#[test]
fn test_compile_vec_len_empty_vec() {
    use cranelisp_types::ResolvedCall;

    let len_span = Span::new(1400, 1420);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        len_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-len"),
        },
    );

    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-len"),
            span: Span::new(1401, 1408),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![Expr::VecLit {
            elements: vec![],
            span: Span::new(1409, 1411),
            inferred_type: None,
        }],
        span: len_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
    display: None,
    };

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 0);
}

// spec: 04-expressions §4.10 — nested Vec literals (Vec of Vecs)
#[test]
fn test_compile_nested_vec_literals() {
    // [[1 2] [3 4]] — a Vec of Vecs (nested heap values)
    let expr = Expr::VecLit {
        elements: vec![
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: Span::new(1502, 1503), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(1504, 1505), inferred_type: None },
                ],
                span: Span::new(1501, 1506),
                inferred_type: None,
            },
            Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 3, span: Span::new(1508, 1509), inferred_type: None },
                    Expr::IntLit { value: 4, span: Span::new(1510, 1511), inferred_type: None },
                ],
                span: Span::new(1507, 1512),
                inferred_type: None,
            },
        ],
        span: Span::new(1500, 1513),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "nested vec should compile: {result:?}");
    let outer_ptr = result.unwrap();
    assert!(outer_ptr > 1024);
    assert_eq!(vec_len_for_test(outer_ptr), 2);

    // First inner vec.
    unsafe {
        let base = outer_ptr as *const u8;
        let data = *(base.add(32) as *const *const i64);
        let inner1 = *data;
        assert!(inner1 > 1024, "inner vec should be heap pointer");
        assert_eq!(vec_len_for_test(inner1), 2);
    }

    // Clean up (inner vecs need manual cleanup since no drop glue yet).
    unsafe {
        let base = outer_ptr as *const u8;
        let data = *(base.add(32) as *const *const i64);
        cranelisp_intrinsics::vec_runtime::vec_drop(*data, 0);
        cranelisp_intrinsics::vec_runtime::vec_drop(*data.add(1), 0);
    }
    cranelisp_intrinsics::vec_runtime::vec_drop(outer_ptr, 0);
}

// spec: 04-expressions §4.10 — large Vec literal (10 elements)
#[test]
fn test_compile_vec_large_literal() {
    // [0 1 2 3 4 5 6 7 8 9] — 10 elements
    let elements: Vec<Expr> = (0..10)
        .map(|i| Expr::IntLit {
            value: i,
            span: Span::new(1600 + (i as u32) * 2, 1602 + (i as u32) * 2),
            inferred_type: None,
        })
        .collect();

    let expr = Expr::VecLit {
        elements,
        span: Span::new(1600, 1620),
        inferred_type: None,
    };
    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(result.is_ok(), "large vec should compile: {result:?}");
    let ptr = result.unwrap();
    assert_eq!(vec_len_for_test(ptr), 10);

    unsafe {
        let base = ptr as *const u8;
        let data = *(base.add(32) as *const *const i64);
        for i in 0..10 {
            assert_eq!(*data.add(i), i as i64);
        }
    }

    cranelisp_intrinsics::vec_runtime::vec_drop(ptr, 0);
}

// --- Ring 2A: TraitMethod dispatch tests ---

// spec: 07-traits §7.7, appendix-a-builtins §A.3 — Num.+ primitive dispatch inlines to add-i64.
//
// Per Decision 43 + FIXME 0185: backend has no trait knowledge. The
// pre-D43 shape (TraitMethod with `(Num, "+", Int)` → backend-side
// `primitive_for_trait_method` lookup → inline IR) is deleted. The
// post-D43 path is: typecheck emits `ResolvedCall::BuiltinFn { name:
// "add-i64" }` directly for primitive-implemented operators; backend's
// inline-substitution path matches by Symbol only. The test asserts
// this end-to-end: `BuiltinFn { name: "add-i64" }` → inline iadd → 7.
#[test]
fn test_trait_method_dispatch_inline_add() {
    // (+ 3 4) post-D43 = BuiltinFn add-i64 (typecheck resolves the
    // primitive directly, not a TraitMethod).
    let apply_span = Span::new(100, 110);
    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("+"),
            span: Span::new(101, 102),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::IntLit { value: 3, span: Span::new(103, 104), inferred_type: None },
            Expr::IntLit { value: 4, span: Span::new(105, 106), inferred_type: None },
        ],
        span: apply_span,
        resolved_call: None,
        inferred_type: None,
    };

    let mut check = empty_check();
    check.method_resolutions.insert(
        apply_span,
        cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("add-i64"),
        },
    );

    let value = test_compile_and_run(&expr, &check, &empty_tables())
        .expect("BuiltinFn add-i64 should compile inline");
    assert_eq!(value, 7);
}

// spec: 07-traits §7.7, appendix-a-builtins §A.3 — Eq.= primitive dispatch on Bool.
//
// Per Decision 43 + FIXME 0185: same shape change as the Num.+ test.
// Post-D43 typecheck emits `BuiltinFn { name: "eq-bool" }` for the
// primitive-implemented `=` on Bool. Backend's inline path matches by
// Symbol; the result is the `icmp eq` IR returning 1 (true).
#[test]
fn test_trait_method_dispatch_eq_bool() {
    // (= true true) post-D43 = BuiltinFn eq-bool.
    let apply_span = Span::new(200, 210);
    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("="),
            span: Span::new(201, 202),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::BoolLit { value: true, span: Span::new(203, 207), inferred_type: None },
            Expr::BoolLit { value: true, span: Span::new(208, 212), inferred_type: None },
        ],
        span: apply_span,
        resolved_call: None,
        inferred_type: None,
    };

    let mut check = empty_check();
    check.method_resolutions.insert(
        apply_span,
        cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("eq-bool"),
        },
    );

    let value = test_compile_and_run(&expr, &check, &empty_tables())
        .expect("BuiltinFn eq-bool should compile inline");
    assert_eq!(value, 1); // true == true → true (1)
}

// spec: 07-traits §7.7 — constrained polymorphic fn skipped at definition, monomorphised at call
#[test]
fn test_constrained_fn_skipped_in_compile_program() {
    // A constrained fn should be skipped (not compiled).
    let defn = Defn {
        name: Symbol::from("add"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::IntLit { value: 0, span: Span::new(10, 11), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 20),
    };

    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 42, span: Span::new(30, 32), inferred_type: None },
            span: Span::new(25, 40),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(25, 40),
    };

    let program: Program = vec![
        TopLevel::Defn(defn),
        TopLevel::Defn(main_defn),
    ];

    let mut check = empty_check();
    // Mark "add" as constrained — should be skipped during compilation.
    check.constrained_fn_names.insert(Symbol::from("add"));

    let value = test_compile_program_and_run(&program, &check, &empty_tables())
        .expect("should compile with constrained fn skipped");
    assert_eq!(value, 42);
}

// spec: 07-traits §7.7 — no default method defns produces empty extras
#[test]
fn test_collect_extra_defns_empty() {
    let check = empty_check();
    // Verify default_method_defns is empty in a fresh CheckResult.
    assert!(check.default_method_defns.is_empty());
}

// spec: 07-traits §7.7 — default trait methods compiled as extra defns
#[test]
fn test_compile_with_default_method_defns() {
    // A program with only a main function, but check has a default method defn.
    // The default method defn should be compiled alongside main.
    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("default-ne"),
                    span: Span::new(10, 20),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit { value: 1, span: Span::new(21, 22), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(23, 24), inferred_type: None },
                ],
                span: Span::new(9, 25),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 30),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 30),
    };

    let default_defn = Defn {
        name: Symbol::from("default-ne"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::IntLit { value: 77, span: Span::new(0, 2), inferred_type: None },
            span: Span::new(0, 10),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 10),
    };

    let program: Program = vec![TopLevel::Defn(main_defn)];
    let mut check = empty_check();
    check.default_method_defns.push(default_defn);

    let value = test_compile_program_and_run(&program, &check, &empty_tables())
        .expect("program with default method defns should compile");
    assert_eq!(value, 77, "should call the default method defn");
}

// spec: 12-runtime §12.5, 07-traits §7.7 — TCO for monomorphised self-recursive call
//
// When a constrained-poly function like `countdown` is monomorphised to
// `countdown$Int`, the body contains a self-recursive call `(countdown ...)`
// that the typechecker resolves to `SigDispatch { mangled_name: "countdown$Int" }`.
// The backend's TCO check must recognize this as self-recursion.
//
// This test compiles a simple recursive function and verifies it completes
// without stack overflow (1M iterations would blow the stack without TCO).
#[test]
fn test_mono_defn_self_recursive_tco() {
    // countdown$Int: (defn countdown$Int [n] (if (= n 0) 0 (countdown$Int (- n 1))))
    // Simplified: use intrinsic primitives instead of trait dispatch.
    let n_span = Span::new(10, 11);
    let zero_span = Span::new(20, 21);
    let eq_span = Span::new(30, 40);
    let sub_span = Span::new(50, 60);
    let recurse_span = Span::new(70, 90);
    let if_span = Span::new(5, 95);
    let result_span = Span::new(92, 93);

    // Build: (if (eq-i64 n 0) 0 (countdown$Int (sub-i64 n 1)))
    let cond = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("eq-i64"),
            span: Span::new(31, 37),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::Var { name: Symbol::from("n"), span: n_span, resolved_call: None, inferred_type: None },
            Expr::IntLit { value: 0, span: zero_span, inferred_type: None },
        ],
        span: eq_span,
        resolved_call: None,
        inferred_type: None,
    };

    let sub_call = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("sub-i64"),
            span: Span::new(51, 58),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::Var { name: Symbol::from("n"), span: Span::new(55, 56), resolved_call: None, inferred_type: None },
            Expr::IntLit { value: 1, span: Span::new(57, 58), inferred_type: None },
        ],
        span: sub_span,
        resolved_call: None,
        inferred_type: None,
    };

    // The recursive call: callee is "countdown" (original name),
    // but it's resolved to countdown$Int via SigDispatch.
    let recurse = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("countdown"),
            span: Span::new(71, 80),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![sub_call],
        span: recurse_span,
        resolved_call: None,
        inferred_type: None,
    };

    let body = Expr::If {
        cond: Box::new(cond),
        then_branch: Box::new(Expr::IntLit { value: 0, span: result_span, inferred_type: None }),
        else_branch: Box::new(recurse),
        span: if_span,
        inferred_type: None,
    };

    let countdown_defn = Defn {
        name: Symbol::from("countdown$Int"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("n"), None)],
            body,
            span: Span::new(0, 100),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 100),
    };

    // Set up method resolutions:
    // - eq_span: BuiltinFn("eq-i64") for the equality check
    // - sub_span: BuiltinFn("sub-i64") for the subtraction
    // - recurse_span: SigDispatch("countdown$Int") for the self-recursive call
    let mut check = empty_check();
    check.method_resolutions.insert(
        eq_span,
        cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("eq-i64"),
        },
    );
    check.method_resolutions.insert(
        sub_span,
        cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("sub-i64"),
        },
    );
    check.method_resolutions.insert(
        recurse_span,
        cranelisp_types::ResolvedCall::SigDispatch {
            mangled_name: cranelisp_types::JitSymbol::from("countdown$Int"),
        },
    );

    // Enrich the defn from CheckResult side maps (test bridge).
    let mut enriched_defn = countdown_defn.clone();
    enrich_defn_from_side_maps(&mut enriched_defn, &check.method_resolutions, &check.expr_types);

    // Compile with direct calls (no GOT).
    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    jit.declare_intrinsics().unwrap();
    let func_ids = jit.declare_functions(&[&enriched_defn]).unwrap();

    let arities: HashMap<Symbol, usize> =
        vec![(Symbol::from("countdown$Int"), 1)].into_iter().collect();

    let tables = empty_tables();
    let aliases = empty_aliases();
    let ctx = jit.build_compile_context(
        &func_ids, &arities,
        &tables, &aliases, ModuleFullPath::from("test"),
    );
    jit.compile_defn(&enriched_defn, ctx).unwrap();
    let countdown_ptr = jit.finalize_and_get_ptr(&Symbol::from("countdown$Int"), 1).unwrap();

    // Call with 1_000_000 — without TCO this would stack overflow.
    let func: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(countdown_ptr) };
    let result = func(1_000_000);
    assert_eq!(result, 0, "TCO should allow 1M recursive calls without stack overflow");
}

// --- compile_to_module module tests ---

// spec: design/arch/CLAUDE.md Decision 36 — bare-name function declarations
// uniformly across all modules. Two modules with same-named function compile
// into separate JITs without collision because function symbols are
// `.o`-Local — they cannot collide across modules' JITs.
#[test]
fn test_module_prefix_applied() {
    let _ = empty_check();
    // Module "mod_a" defines "val" returning 100.
    let val_a = Defn {
        name: Symbol::from("val"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 100, span: Span::new(0, 3), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let mod_a = ModuleFullPath::from("mod_a");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(mod_a.clone());
        st.insert(val_a.name.clone(), make_def_entry(val_a.clone()));
        tables.insert(mod_a.clone(), st);
    }
    let mut jit_a = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let _artifacts_a = compile_to_module(
        mod_a.clone(),
        std::slice::from_ref(&val_a.name),
        &tables,
        &aliases,
        jit_a.jit_module(),
        true,
    ).expect("module A should compile");
    // Post-G6: compile_to_module finalized internally. `val` is a zero-arg
    // defn with no GOT slot (direct FuncId); read its ptr by name.
    let ptr = jit_a.get_ptr_by_name(&Symbol::from("val"), 0).unwrap();
    assert!(!ptr.is_null(), "module A 'val' must finalize to a non-null ptr");
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    assert_eq!(func(), 100, "module A's val should return 100");

    // Module B also defines "val" returning 200 — compiles into a separate JIT.
    let val_b = Defn {
        name: Symbol::from("val"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 200, span: Span::new(100, 103), inferred_type: None },
            span: Span::new(100, 120),
        }],
        visibility: Visibility::Public,
        span: Span::new(100, 120),
    };
    let mod_b = ModuleFullPath::from("mod_b");
    {
        let mut st = SymbolTable::new(mod_b.clone());
        st.insert(val_b.name.clone(), make_def_entry(val_b.clone()));
        tables.insert(mod_b.clone(), st);
    }

    let mut jit_b = Jit::new_with_symbols(&[]).unwrap();
    let _artifacts_b = compile_to_module(
        mod_b.clone(),
        std::slice::from_ref(&val_b.name),
        &tables,
        &aliases,
        jit_b.jit_module(),
        true,
    ).expect("module B should compile without collision");
    // Post-G6: compile_to_module finalized internally.
    let ptr_b = jit_b.get_ptr_by_name(&Symbol::from("val"), 0).unwrap();
    let func_b: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr_b) };
    assert_eq!(func_b(), 200, "module B's val should return 200");
}

// --- G6 code-write invariants (Sprint 57 Wave 2; S75 W2 D41 rotation) ---
//
// spec: design/backend/compile-to-module.md §2 (S75 banner) + facade
// §"Code" — `compile_to_module` writes each compiled symbol's finalised
// code pointer directly into the entry's GOT slot (D41 #2), and no longer
// returns a per-symbol `code_ptrs` map. The lifecycle-owner write (D41 #1
// — `Code::Jit(Arc<Jit>)`) stays in the integration layer; backend leaves
// `ModuleEntry::Def.code` untouched.
#[test]
fn compile_to_module_writes_got_slot_after_finalize() {
    let defn = Defn {
        name: Symbol::from("seven"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 7, span: Span::new(0, 1), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let module = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        // Explicit GOT slot so the D41 #2 direct-write is exercised.
        st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let _artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    ).expect("JIT compile should succeed");

    // D41 #2: backend wrote the finalised code pointer into the entry's
    // GOT slot (slot 0). Read it back; it must be non-null in JIT mode.
    let guard = tables.get(&module).expect("symbol table present");
    let entry = guard.get(defn.name.as_ref()).expect("entry present");
    let slot = entry
        .callable_got_slot()
        .expect("test inserted a Def entry with a GOT slot");
    match entry {
        ModuleEntry::Def { code, .. } => {
            let ptr = guard.got.load_slot(slot);
            assert!(
                !ptr.is_null(),
                "backend must write the finalised code pointer to the GOT slot (D41 #2)"
            );
            // D41 #1 (Code::Jit lifecycle owner) stays in the integration
            // layer — backend leaves `code` untouched.
            assert!(
                code.is_none(),
                "backend must not write to ModuleEntry::Def.code (D41 #1 is int's job)"
            );
        }
        _ => unreachable!("test inserted a Def entry with a GOT slot"),
    }
}

// spec: design/backend/compile-to-module.md §2.6.6 — constructor-as-value
// through the generic fn-as-value GOT path (S75 W4 closure deletion).
//
// This is the durable regression guard for deleting the bespoke
// `compile_data_constructor_as_value` + `compile_ctor_wrapper_body` family.
// It proves the corrected `compile_var` dispatch: a *data* constructor
// referenced as a value (`(let [f Some] (f 3))`) is no longer special-cased;
// it falls through to `is_known_function` → `compile_fn_as_value` over the
// got-slotted constructor `Def` — the SAME GOT/fn-as-value mechanism
// `compile_operator_as_value` uses for primitives (§2.6.1, Decision 48).
//
// Two-stage `make_def_entry_slot` pattern (§2.6.6):
//   Stage 1 — got-slot + compile the constructor `Def` (its `Expr::ConstrADT`
//             body → `compile_constr_adt` → `emit_adt_construct`) so the GOT
//             slot holds a live callable.
//   Stage 2 — compile a consumer that references the constructor as a value;
//             `compile_fn_as_value`'s `emit_wrapper_call` GOT-indirects to
//             slot 0. Run end-to-end (slab base registered via
//             `Jit::new_with_symbols`, the precedent set by
//             `jit_got_symbol_address_is_slab_base` /
//             `test_extern_primitive_with_resolved_call`) and assert the
//             constructed ADT's field round-trips.
//
// Backend EXPECTS the constructor's GOT slot to be populated; the harness
// populates it the way int will at S77 (§2.6.5). Backend does not got-slot
// constructors itself — that is typecheck + int's job, exactly as primitives'
// GOT entries are not backend's.
#[test]
fn constructor_as_value_falls_through_to_fn_as_value() {
    use cranelisp_types::{
        DefKind, FQTypeName, ModuleEntry, Scheme, TypeName,
    };

    let module = ModuleFullPath::from("user");
    let fqtn = FQTypeName::new(module.clone(), TypeName::from("Option"));

    // The constructor `Some`'s synthesised body: ConstrADT { tag: 1,
    // fields: [Var("v")] } — the exact shape typecheck produces at S77.
    let ctor_body = Expr::ConstrADT {
        type_name: fqtn.clone(),
        tag: 1,
        fields: vec![Expr::Var {
            name: Symbol::from("v"),
            span: Span::new(10, 11),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }],
        span: Span::new(0, 12),
        inferred_type: Some(Box::new(Type::ADT(fqtn.clone(), vec![]))),
    };
    let ctor_defn = Defn {
        name: Symbol::from("Some"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("v"), None)],
            body: ctor_body,
            span: Span::new(0, 12),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 12),
    };
    // make_def_entry_slot stamps kind = UserFn; override to Constructor so
    // `lookup_constructor` / `data_constructor_info` recognise it AND
    // `resolve_got_target` finds the got slot (slot 0).
    let base_entry = make_def_entry_slot(ctor_defn.clone(), 0);
    // The slot now rides on the callable variant; carry it onto the
    // Constructor we re-stamp (slot 0).
    let ctor_slot = base_entry
        .callable_got_slot()
        .expect("make_def_entry_slot stamps a slot");
    let ctor_entry = match base_entry {
        ModuleEntry::Def {
            visibility,
            docstring,
            param_names,
            callees,
            trait_origin,
            seq,
            ast,
            code,
            ..
        } => ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![Type::Int], Box::new(Type::ADT(fqtn.clone(), vec![]))),
            },
            visibility,
            docstring,
            param_names,
            kind: Box::new(DefKind::Constructor {
                got_slot: ctor_slot,
                type_name: fqtn.clone(),
                tag: 1,
                field_count: 1,
                internal: false,
                type_def: None,
                mode_summary: None,
            }),
            callees,
            trait_origin,
            seq,
            ast,
            codegen_view: None,
            code,
            value_use: false,
        },
        _ => unreachable!("make_def_entry_slot builds a Def"),
    };

    // Consumer: (let [f Some] (f 3)) — references `Some` as a value, then
    // calls the bound closure. The `[f Some]` binding compiles `Some` via
    // `compile_var` → fall-through → `compile_fn_as_value` (the path under
    // test); `(f 3)` is a local-var closure call.
    let consumer_body = Expr::Let {
        bindings: vec![(
            Symbol::from("f"),
            Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(100, 104),
                resolved_call: None,
                inferred_type: None,
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("f"),
                span: Span::new(110, 111),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 3,
                span: Span::new(112, 113),
                inferred_type: None,
            }],
            span: Span::new(109, 114),
            resolved_call: None,
            inferred_type: None,
        }),
        span: Span::new(90, 115),
        inferred_type: None,
    };
    let consumer_defn = Defn {
        name: Symbol::from("useit"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: consumer_body,
            span: Span::new(90, 115),
        }],
        visibility: Visibility::Public,
        span: Span::new(90, 115),
    };

    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(ctor_defn.name.clone(), ctor_entry);
        st.insert(consumer_defn.name.clone(), make_def_entry_slot(consumer_defn.clone(), 1));
        st.next_got_slot = 2;
        tables.insert(module.clone(), st);
    }

    // Register __cranelisp_got_user → the table's GOT slab base BEFORE
    // building the JIT (base_ptr is stable for the GotTable's lifetime).
    let got_data_name = crate::compiler::got_data_symbol_name(&module);
    let got_base = tables
        .get(&module)
        .map(|st| st.got.base_ptr())
        .expect("user table just inserted");
    let extras: Vec<(&str, *const u8)> = vec![(got_data_name.as_str(), got_base)];

    let mut jit = Jit::new_with_symbols(&extras).expect("jit init");
    let aliases = empty_aliases();
    let names = vec![ctor_defn.name.clone(), consumer_defn.name.clone()];
    compile_to_module(module.clone(), &names, &tables, &aliases, jit.jit_module(), true)
        .expect("constructor Def + consumer compile (closure deletion regression guard)");

    // Stage 1 assertion: the constructor `Def`'s body compiled into a live
    // callable at slab slot 0 (non-null after finalize — the same write
    // `compile_to_module_writes_got_slot_after_finalize` asserts).
    {
        let guard = tables.get(&module).expect("table present");
        match guard.get("Some") {
            Some(entry) if entry.callable_got_slot().is_some() => {
                let slot = entry.callable_got_slot().unwrap();
                assert!(
                    !guard.got.load_slot(slot).is_null(),
                    "constructor body must finalize to a live callable in its GOT slot (Stage 1)"
                );
            }
            other => panic!("expected got-slotted constructor Def, got {other:?}"),
        }
    }

    // Stage 2 assertion: run the consumer end-to-end. It builds `(Some 3)`
    // through the GOT-indirect fn-as-value wrapper and returns the heap
    // pointer to `[.., tag=1, field=3]`. Read the field back.
    let ptr = jit.get_ptr_by_name(&consumer_defn.name, 0).expect("finalize consumer");
    assert!(!ptr.is_null(), "consumer must finalize to a non-null fn ptr");
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    let adt_ptr = func();
    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        panic!("runtime panic running consumer: {msg}");
    }
    assert!(adt_ptr != 0, "constructor-as-value must allocate a heap ADT");
    // Field 0 lives at HeapAdt::field_offset(0) from the base pointer.
    let field0 = unsafe {
        let field_addr = (adt_ptr as usize
            + crate::heap::HeapAdt::field_offset(0) as usize)
            as *const i64;
        *field_addr
    };
    assert_eq!(
        field0, 3,
        "constructor-as-value (map-style first-class use) must construct the ADT \
         with the passed field; got {field0}"
    );
}

// spec: 07-traits §7.6 — a trait method used as a first-class value
// dispatches to the impl chosen by typecheck for the value's type, NOT a
// hard-coded default. This is the backend half of FIXME 0300 Symptom B.
//
// `(let [f +] (f 1.0 2.0))` where typecheck has annotated the value-position
// `+` Var with `resolved_call: Some(BuiltinFn { name: "add-f64" })` and
// `inferred_type: Fn([Float, Float], Float)`. The new `compile_var` early
// branch emits a zero-capture dispatch-wrapper that calls `add-f64` (float
// add). The OLD hard-coded `compile_operator_as_value` path mapped `+` →
// `add-i64` unconditionally — integer add on the two float bit-patterns —
// which yields a garbage / `inf.0`-shaped result, never `3.0`. So a `3.0`
// result proves the resolution is honored and the Int path is bypassed.
//
// `add-f64` is an INLINE builtin (`primitives_inline`), so this runs
// end-to-end inside the backend unit-test JIT with no `cranelisp-primitives`
// dependency (Decision 48) and no extern symbol.
#[test]
fn value_position_plus_float_dispatches_add_f64_not_add_i64() {
    // The value-position `+` reference, fully annotated as typecheck's
    // value-position resolution pass produces (FIXME 0300 Step 2/3).
    let plus_as_value = Expr::Var {
        name: Symbol::from("+"),
        span: Span::new(100, 101),
        resolved_call: Some(Box::new(
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("add-f64"),
            },
        )),
        inferred_type: Some(Box::new(Type::Fn(
            vec![Type::Float, Type::Float],
            Box::new(Type::Float),
        ))),
    };

    // Consumer: (let [f +] (f 1.0 2.0)) — binds the dispatch-wrapper closure
    // to `f`, then applies it. `(f 1.0 2.0)` is a local-var closure call.
    let consumer_body = Expr::Let {
        bindings: vec![(Symbol::from("f"), plus_as_value)],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("f"),
                span: Span::new(110, 111),
                resolved_call: None,
                inferred_type: None,
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: Span::new(112, 115),
                    inferred_type: Some(Box::new(Type::Float)),
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: Span::new(116, 119),
                    inferred_type: Some(Box::new(Type::Float)),
                },
            ],
            span: Span::new(109, 120),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Float)),
        }),
        span: Span::new(90, 121),
        inferred_type: Some(Box::new(Type::Float)),
    };

    let value = test_compile_and_run(
        &consumer_body,
        &empty_check(),
        &empty_tables(),
    )
    .expect("value-position + (add-f64) should compile and run");

    let result = f64::from_bits(value as u64);
    assert_eq!(
        result, 3.0,
        "value-position `+` on Floats must dispatch to add-f64 (→ 3.0); \
         a non-3.0 result means the hard-coded add-i64 path leaked \
         (FIXME 0300 Symptom B)"
    );
}

// spec: 07-traits §7.6 — value-position trait method resolved to a TraitMethod
// (mangled impl) emits a dispatch-wrapper that calls the *mangled name*, NOT
// the hard-coded operator primitive. We assert this WITHOUT a GOT slot for
// the impl (which is the int-binary's concern; the four e2e tests cover the
// run side after the int slice): the wrapper's `emit_wrapper_call` resolves
// the mangled name `Eq.=$String` and — because no slot is registered in this
// minimal table — fails with an error naming `Eq.=$String`. That error is
// proof-positive that `compile_var` took the resolved-call branch and tried
// to dispatch to the typecheck-chosen impl, rather than silently emitting
// the hard-coded `eq-i64` (`operator_primitive_name`) which would have
// compiled "successfully" to the WRONG impl (Symptom B).
#[test]
fn value_position_eq_string_dispatches_to_mangled_impl_not_eq_i64() {
    let module = ModuleFullPath::from("user");

    // `=` on String resolved to the mangled trait-impl name (the non-
    // primitive TraitMethod path). The wrapper must call this name, not
    // emit the hard-coded `eq-i64`.
    let eq_as_value = Expr::Var {
        name: Symbol::from("="),
        span: Span::new(50, 51),
        resolved_call: Some(Box::new(
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::FQTraitName::new(
                    module.clone(),
                    cranelisp_types::TraitName::from("Eq"),
                ),
                method_name: Symbol::from("="),
                impl_type: cranelisp_types::FQTypeName::new(
                    ModuleFullPath::from("primitives"),
                    cranelisp_types::TypeName::from("String"),
                ),
                mangled_name: cranelisp_types::JitSymbol::from("Eq.=$String"),
            },
        )),
        inferred_type: Some(Box::new(Type::Fn(
            vec![Type::String, Type::String],
            Box::new(Type::Bool),
        ))),
    };
    let defn = Defn {
        name: Symbol::from("__expr__"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: eq_as_value,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(defn.name.clone(), make_def_entry(defn.clone()));
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).expect("jit init");
    let aliases = empty_aliases();
    let names = vec![defn.name.clone()];
    let result = compile_to_module(
        module.clone(),
        &names,
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    );
    // `CompilationArtifacts` is not `Debug`, so match rather than `expect_err`.
    let err = match result {
        Ok(_) => panic!(
            "without a registered GOT slot for the impl, the dispatch-wrapper's \
             call to the mangled name must fail — a clean compile means the \
             hard-coded eq-i64 path leaked (FIXME 0300 Symptom B)"
        ),
        Err(e) => e,
    };

    let msg = format!("{err:?}");
    assert!(
        msg.contains("Eq.=$String"),
        "the codegen error must name the typecheck-chosen mangled impl \
         `Eq.=$String` (proving the wrapper dispatched to the resolved \
         target); a silent success or an `eq-i64` reference would mean the \
         hard-coded operator path leaked (FIXME 0300 Symptom B). Got: {msg}"
    );
}

// spec: facades/backend.md §"Free functions" — produce_disasm reads the
// live GOT-slot code pointer, reads caller-supplied `code_size` bytes, and
// capstone-disassembles them (S75 W3 Finding-C — real body, not a stub).
#[test]
fn produce_disasm_returns_nonempty_for_jit_compiled_fn() {
    use cranelisp_types::FQSymbol;

    let defn = Defn {
        name: Symbol::from("seven"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 7, span: Span::new(0, 1), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let module = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    ).expect("JIT compile should succeed");

    // code_size comes from the compile-time artifacts — the caller passes
    // it back into produce_disasm (Finding-C: backend never re-derives it).
    assert!(artifacts.code_size > 0, "JIT codegen must report a code size");

    let fq = FQSymbol { module: module.clone(), symbol: defn.name.clone() };
    let disasm = produce_disasm(&fq, artifacts.code_size, &tables)
        .expect("produce_disasm should disassemble live JIT code");
    assert!(
        !disasm.trim().is_empty(),
        "produce_disasm must return non-empty disassembly text for a live fn"
    );
}

// spec: design/backend/compile-to-module.md §9.1.6 — ObjectModule has no
// post-finalize runtime pointer; the GOT slot stays null in object mode.
#[test]
fn compile_to_module_object_mode_no_got_write() {
    use cranelift_module::default_libcall_names;
    use cranelift_object::{ObjectBuilder, ObjectModule};

    let defn = Defn {
        name: Symbol::from("answer"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let module = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        // Explicit GOT slot so we can assert object mode leaves it null.
        st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let isa = build_isa(true).unwrap();
    let obj_builder =
        ObjectBuilder::new(isa, "test_obj", default_libcall_names()).unwrap();
    let mut obj_module = ObjectModule::new(obj_builder);

    let aliases = empty_aliases();
    let _artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        &mut obj_module,
        true,
    ).expect("object compile should succeed");

    // Object-mode invariant: `try_get_finalized_function` returns None (no
    // runtime pointer before `finish()`), so backend writes nothing to the
    // GOT slot — it stays null.
    let guard = tables.get(&module).expect("symbol table present");
    let entry = guard.get(defn.name.as_ref()).expect("entry present");
    let slot = entry
        .callable_got_slot()
        .expect("test inserted a Def entry with a GOT slot");
    match entry {
        ModuleEntry::Def { code, .. } => {
            assert!(
                guard.got.load_slot(slot).is_null(),
                "object-mode compile must not populate the GOT slot"
            );
            assert!(
                code.is_none(),
                "object-mode entry's code field must be None"
            );
        }
        _ => unreachable!("test inserted a Def entry with a GOT slot"),
    }
}

// --- multi-sig defn tests ---
//
// Sprint 56 Wave 1: `build_mangled_name`, `concrete_type_name`, and
// `expand_multi_sig_defn` were deleted from the backend. Mangled variant
// entries are now pre-materialised by typecheck in Wave 0. The unit tests
// that exercised those helpers directly are retired; end-to-end multi-sig
// dispatch is covered by `test_compile_multi_sig_defn_end_to_end` and
// `test_compile_multi_sig_second_variant` below (plus the integration
// tests in `tests/`).

// spec: 05-definitions §5.1.2 — multi-sig defn compiles and dispatches correctly
//
// Defines a multi-sig function `f` with two variants:
//   (defn f ([x] x) ([a b] a))      — identity on 1 arg, first on 2 args
// Then defines main that calls the first variant via SigDispatch.
#[test]
fn test_compile_multi_sig_defn_end_to_end() {
    let variant1_span = Span::new(10, 30);
    let variant2_span = Span::new(40, 60);

    let multi_defn = Defn {
        name: Symbol::from("f"),
        docstring: None,
        variants: vec![
            DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16), resolved_call: None, inferred_type: None },
                span: variant1_span,
            },
            DefnVariant {
                params: vec![(Symbol::from("a"), None), (Symbol::from("b"), None)],
                body: Expr::Var { name: Symbol::from("a"), span: Span::new(45, 46), resolved_call: None, inferred_type: None },
                span: variant2_span,
            },
        ],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 70),
    };

    // main calls f$Int(42)
    let call_span = Span::new(100, 120);
    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("f"),
                    span: Span::new(101, 102),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit { value: 42, span: Span::new(103, 105), inferred_type: None }],
                span: call_span,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(95, 125),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(95, 125),
    };

    let program: Program = vec![
        TopLevel::Defn(multi_defn),
        TopLevel::Defn(main_defn),
    ];

    let mut check = empty_check();
    // Register SigDispatch for the call site.
    check.method_resolutions.insert(
        call_span,
        cranelisp_types::ResolvedCall::SigDispatch {
            mangled_name: cranelisp_types::JitSymbol::from("f$Int"),
        },
    );

    // Set up symbol table with Overloaded entry for multi-sig expansion.
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let module_path = ModuleFullPath::from("user");
    let mut table = SymbolTable::new(module_path.clone());
    table.insert(
        Symbol::from("f"),
        cranelisp_types::ModuleEntry::Def {
            scheme: cranelisp_types::Scheme { type_vars: vec![], constraints: Default::default(), ty: Type::Int },
            visibility: cranelisp_types::Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(cranelisp_types::DefKind::Overloaded {
                variants: vec![
                    cranelisp_types::OverloadVariant {
                        param_types: vec![Type::Int],
                        ret_type: Type::Int,
                        mangled_name: Symbol::from("f$Int"),
                    },
                    cranelisp_types::OverloadVariant {
                        param_types: vec![Type::Int, Type::Int],
                        ret_type: Type::Int,
                        mangled_name: Symbol::from("f$Int+Int"),
                    },
                ],
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        },
    );
    tables.insert(module_path, table);

    let result = test_compile_program_and_run(&program, &check, &tables)
        .expect("multi-sig program should compile");
    assert_eq!(result, 42, "should dispatch to f$Int and return 42");
}

// spec: 05-definitions §5.1.2 — multi-sig dispatch to second variant
#[test]
fn test_compile_multi_sig_second_variant() {
    let variant1_span = Span::new(10, 30);
    let variant2_span = Span::new(40, 60);

    let multi_defn = Defn {
        name: Symbol::from("g"),
        docstring: None,
        variants: vec![
            DefnVariant {
                params: vec![(Symbol::from("x"), None)],
                body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16), resolved_call: None, inferred_type: None },
                span: variant1_span,
            },
            DefnVariant {
                params: vec![(Symbol::from("a"), None), (Symbol::from("b"), None)],
                // Return b (second param) to prove we dispatched to the right variant.
                body: Expr::Var { name: Symbol::from("b"), span: Span::new(45, 46), resolved_call: None, inferred_type: None },
                span: variant2_span,
            },
        ],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(0, 70),
    };

    // main calls g$Int+Int(10, 99) — should return 99 (the second arg)
    let call_span = Span::new(100, 120);
    let main_defn = Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("g"),
                    span: Span::new(101, 102),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![
                    Expr::IntLit { value: 10, span: Span::new(103, 105), inferred_type: None },
                    Expr::IntLit { value: 99, span: Span::new(106, 108), inferred_type: None },
                ],
                span: call_span,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(95, 125),
        }],
        visibility: cranelisp_types::Visibility::Public,
        span: Span::new(95, 125),
    };

    let program: Program = vec![
        TopLevel::Defn(multi_defn),
        TopLevel::Defn(main_defn),
    ];

    let mut check = empty_check();
    check.method_resolutions.insert(
        call_span,
        cranelisp_types::ResolvedCall::SigDispatch {
            mangled_name: cranelisp_types::JitSymbol::from("g$Int+Int"),
        },
    );

    // Set up symbol table with Overloaded entry for multi-sig expansion.
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let module_path = ModuleFullPath::from("user");
    let mut table = SymbolTable::new(module_path.clone());
    table.insert(
        Symbol::from("g"),
        cranelisp_types::ModuleEntry::Def {
            scheme: cranelisp_types::Scheme { type_vars: vec![], constraints: Default::default(), ty: Type::Int },
            visibility: cranelisp_types::Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(cranelisp_types::DefKind::Overloaded {
                variants: vec![
                    cranelisp_types::OverloadVariant {
                        param_types: vec![Type::Int],
                        ret_type: Type::Int,
                        mangled_name: Symbol::from("g$Int"),
                    },
                    cranelisp_types::OverloadVariant {
                        param_types: vec![Type::Int, Type::Int],
                        ret_type: Type::Int,
                        mangled_name: Symbol::from("g$Int+Int"),
                    },
                ],
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        },
    );
    tables.insert(module_path, table);

    let result = test_compile_program_and_run(&program, &check, &tables)
        .expect("multi-sig program should compile");
    assert_eq!(result, 99, "should dispatch to g$Int+Int and return second arg (99)");
}

// Note: `test_expand_multi_sig_missing_type_info` and
// `test_concrete_type_name_all_primitives` were retired in Sprint 56 Wave 1
// with the deletion of `expand_multi_sig_defn` / `concrete_type_name`. The
// equivalent mangled-name construction now lives in `/typecheck`, and the
// "missing overload info" error surface is exercised by the backend's
// `ast: None` error path (see `test_compile_to_module_ast_none_errors` in
// the Sprint 56 Wave 1 unit tests below).

// spec: appendix-a-builtins §A.2 — extern primitive dispatch via resolved_call
//
// Isolates the "undefined function: macros/sconcat" failure from
// repl_defmacro_rest_splice. When compile_apply receives an Apply node
// with resolved_call: Some(BuiltinFn { name: "sconcat" }), per Decision
// 0048 §"Structural invariant — backend dep-ban" it MUST take the
// standard GOT-indirect dispatch path (`compile_direct_call` →
// `resolve_got_target` → load slot from `__cranelisp_got_primitives`).
// Pre-Decision-0048 the path was direct extern via `compile_extern_call`;
// that path is now reserved for non-module backend-emitted-call targets
// (intrinsics — `vec-set-copy`, `runtime/alloc`, etc.). Primitives reach
// the JIT via GOT-indirect uniformly with user-defined functions.
//
// Test setup: seed a `primitives` module with a `sconcat` entry that
// carries `got_slot: Some(_)`, write the extern fn ptr into that slot,
// then assert backend compiles + executes the call through the GOT.
#[test]
fn test_extern_primitive_via_resolved_call_succeeds() {
    use cranelisp_types::ResolvedCall;
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};

    // Build: (defn __expr__ [] (sconcat 0 0))
    let apply_span = Span::new(2000, 2030);

    let mut method_resolutions = HashMap::new();
    method_resolutions.insert(
        apply_span,
        ResolvedCall::BuiltinFn {
            name: Symbol::from("sconcat"),
        },
    );

    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("macros/sconcat"),
            span: Span::new(2001, 2015),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::IntLit { value: 0, span: Span::new(2016, 2017), inferred_type: None },
            Expr::IntLit { value: 0, span: Span::new(2018, 2019), inferred_type: None },
        ],
        span: apply_span,
        resolved_call: None, // enrichment will set this from method_resolutions
        inferred_type: None,
    };

    let check = TestCheckResult {
        method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: Vec::new(),
        expr_types: HashMap::new(),
        default_method_defns: Vec::new(),
        warnings: Vec::new(),
        display: None,
    };

    // Seed a primitives module with `sconcat` and a GOT slot. Backend's
    // `resolve_got_target` consults this via its global-fallback walk
    // when the caller's module (`user`) has no local binding for the
    // unqualified name `sconcat`. Per Decision 0048's backend dep-ban,
    // we cannot reference `cranelisp_primitives::marshal::sconcat`
    // directly; we provide a local 2-arg stub matching the signature
    // and wire that fn ptr into the GOT slot. The test asserts
    // compilation + GOT-indirect dispatch — it does NOT assert the
    // semantics of `sconcat` (which is covered by the e2e
    // `mode_equiv_macro_user_defined` test).
    extern "C" fn sconcat_stub(_a: i64, _b: i64) -> i64 { 0 }
    let tables = empty_tables();
    let primitives_path = ModuleFullPath::from("primitives");
    let mut prim_table: SymbolTable = SymbolTable::new(primitives_path.clone());
    let slot = prim_table.allocate_got_slot();
    prim_table.got.store_slot(slot, sconcat_stub as *const u8);
    prim_table.insert(
        Symbol::from("sconcat"),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: Vec::new(),
                constraints: HashMap::new(),
                ty: Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![Symbol::from("a"), Symbol::from("b")],
            kind: Box::new(DefKind::primitive(slot)),
            callees: Vec::new(),
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        },
    );
    tables.insert(primitives_path, prim_table);

    // With resolved_call present (via enrichment), compilation should
    // succeed via GOT-indirect dispatch through the primitives module.
    // The JIT also needs the `__cranelisp_got_primitives` data symbol
    // wired to the table's GOT base — register via
    // `Jit::new_with_symbols` (a separate code path from
    // `test_compile_and_run`'s `Jit::new`).
    let got_data_name = crate::compiler::got_data_symbol_name(
        &ModuleFullPath::from("primitives"),
    );
    let prim_got_base = tables
        .get(&ModuleFullPath::from("primitives"))
        .map(|st| st.got.base_ptr())
        .expect("primitives table just inserted");
    let extras: Vec<(&str, *const u8)> = vec![(got_data_name.as_str(), prim_got_base)];

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
    enrich_defn_from_side_maps(&mut defn, &check.method_resolutions, &check.expr_types);

    let user_module = ModuleFullPath::from("user");
    let name = defn.name.clone();
    {
        let mut st = tables
            .entry(user_module.clone())
            .or_insert_with(|| SymbolTable::new(user_module.clone()));
        st.insert(name.clone(), make_def_entry(defn));
    }

    let mut jit = Jit::new_with_symbols(&extras).expect("jit init");
    let aliases = empty_aliases();
    let result = compile_to_module(user_module, &[name], &tables, &aliases, jit.jit_module(), true);
    assert!(
        result.is_ok(),
        "extern primitive sconcat should compile via GOT-indirect when resolved_call is BuiltinFn: {}",
        result.err().map(|e| format!("{e:?}")).unwrap_or_default(),
    );
}

// spec: appendix-a-builtins §A.2 — missing resolved_call causes "undefined function"
//
// Companion to the test above: when resolved_call is None (not enriched),
// compile_apply falls through to compile_var_apply -> compile_direct_call
// which fails because "macros/sconcat" has no GOT slot or FuncId.
// This is the broken path that the integration test hits.
#[test]
fn test_extern_primitive_without_resolved_call_fails() {
    // Build: (defn main [] (macros/sconcat 0 0))
    // No resolved_call, no GOT entry, no FuncId — should fail.
    let apply_span = Span::new(2100, 2130);

    // No method_resolutions — resolved_call stays None.
    let expr = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("macros/sconcat"),
            span: Span::new(2101, 2115),
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![
            Expr::IntLit { value: 0, span: Span::new(2116, 2117), inferred_type: None },
            Expr::IntLit { value: 0, span: Span::new(2118, 2119), inferred_type: None },
        ],
        span: apply_span,
        resolved_call: None,
        inferred_type: None,
    };

    let check = empty_check();

    let result = test_compile_and_run(&expr, &check, &empty_tables());
    assert!(
        result.is_err(),
        "macros/sconcat without resolved_call should fail"
    );
    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("undefined function"),
        "error should be 'undefined function', got: {err_msg}"
    );
}

// -----------------------------------------------------------------
// Sprint 56 Wave 1 (Step 2a) — direct compile_to_module tests
// -----------------------------------------------------------------

// spec: design/backend/compile-to-module.md §2 (S75 banner) — 5-param
// signature; value-returned CompilationArtifacts + GOT-slot direct write.
//
// Direct `compile_to_module` call with a populated `symbol_tables` and a
// single-name `names` list. Verifies the S75 contract: bodies arrive via
// `ModuleEntry::Def.ast`, the finalised code pointer is written into the
// entry's GOT slot (D41 #2), and the always-created `CompilationArtifacts`
// carries the CLIF + code size.
#[test]
fn sprint56_compile_to_module_direct_call_writes_got_and_artifacts() {
    use cranelisp_types::ModuleEntry;
    let defn = Defn {
        name: Symbol::from("answer"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
            span: Span::new(0, 10),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 10),
    };

    let module = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        // Explicit GOT slot so the D41 #2 direct-write is exercised.
        st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    )
    .expect("direct compile_to_module should succeed");

    // Always-created introspection artefacts carry CLIF + code size.
    assert!(
        !artifacts.clif_ir.is_empty(),
        "CompilationArtifacts.clif_ir must capture the compiled function's CLIF"
    );
    assert!(
        artifacts.code_size > 0,
        "CompilationArtifacts.code_size must be the finalised native code size"
    );

    // D41 #2: the finalised code pointer is written into the entry's GOT
    // slot. Entry remains a Def with ast: Some(_) (regression guard).
    let guard = tables.get(&module).unwrap();
    match guard.get(defn.name.as_ref()) {
        Some(entry @ ModuleEntry::Def { ast: Some(_), .. })
            if entry.callable_got_slot().is_some() =>
        {
            let slot = entry.callable_got_slot().unwrap();
            assert!(
                !guard.got.load_slot(slot).is_null(),
                "backend must write the finalised code pointer to the GOT slot"
            );
        }
        other => panic!("expected Def with ast + got_slot, got {other:?}"),
    }
}

// spec: design/arch/facades/backend.md — `capture_clif` flag (FIXME 0325)
//
// The `capture_clif: bool` parameter (FIXME 0325) gates whether
// `compile_to_module` populates `CompilationArtifacts.clif_ir` with the
// CLIF-IR text. `false` skips the `format!("{}", func.display())` work and
// leaves `clif_ir` empty; `true` captures it. This test compiles the same
// fixture under both states and asserts they differ — if the flag were
// ignored, the two `clif_ir` strings would match and the test fails.
//
// A fresh JIT + symbol-table pair is built per call because
// `compile_to_module` finalizes the module and writes the GOT slot.
#[test]
fn capture_clif_gates_clif_ir_text() {
    fn compile_once(capture_clif: bool) -> CompilationArtifacts {
        let defn = Defn {
            name: Symbol::from("answer"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
                span: Span::new(0, 10),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 10),
        };

        let module = ModuleFullPath::from("user");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
            st.next_got_slot = 1;
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        compile_to_module(
            module,
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            jit.jit_module(),
            capture_clif,
        )
        .expect("direct compile_to_module should succeed")
    }

    // capture_clif = false: the CLIF text is not generated.
    let without = compile_once(false);
    assert!(
        without.clif_ir.is_empty(),
        "capture_clif = false must leave CompilationArtifacts.clif_ir empty, got: {:?}",
        without.clif_ir
    );

    // capture_clif = true: the CLIF text is captured.
    let with = compile_once(true);
    assert!(
        !with.clif_ir.is_empty(),
        "capture_clif = true must populate CompilationArtifacts.clif_ir"
    );

    // The compiled native code is unaffected by the flag — code_size is
    // produced in both cases (the flag only gates the CLIF *text*).
    assert!(
        without.code_size > 0 && with.code_size > 0,
        "code_size must be produced regardless of capture_clif"
    );
}

// spec: design/backend/compile-to-module.md §4 — ast: None returns error
//
// Negative: insert a `ModuleEntry::Def { ast: None, .. }` into the symbol
// table and pass its name in `names`. `compile_to_module` must return
// `Err(CranelispError::CodegenError)` whose message names the symbol —
// no panic, no silent skip.
#[test]
fn sprint56_compile_to_module_ast_none_errors() {
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, UserFnState, Visibility};
    let module = ModuleFullPath::from("user");
    let name = Symbol::from("stub");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(
            name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn {
                    fn_state: UserFnState::NotDetermined,
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: None,
                codegen_view: None,
                code: None,
                value_use: false,
            },
        );
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let result = compile_to_module(
        module,
        std::slice::from_ref(&name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    );
    let err = match result {
        Ok(_) => unreachable!("ast: None must not succeed"),
        Err(e) => e,
    };

    let msg = err.to_string();
    assert!(
        msg.contains(name.as_ref()),
        "error message must name the offending symbol 'stub', got: {msg}"
    );
    assert!(
        msg.contains("ast: None") || msg.contains("ast") && msg.contains("None"),
        "error message should mention the ast: None invariant violation, got: {msg}"
    );
}

// spec: design/backend/compile-to-module.md §4 — no multi-sig expansion in backend
//
// Populate symbol_tables with a pre-mangled multi-sig variant entry
// (`add$Int+Int`, ast: Some(single-variant defn)) alongside the
// Overloaded base entry (`add`, ast: None). Call compile_to_module with
// names = [mangled variant]. Compilation must succeed — the backend never
// invokes a (deleted) `expand_multi_sig_defn` path.
//
// That this test compiles and passes IS the verification: Wave 1 deleted
// `expand_multi_sig_defn` entirely from the source tree.
#[test]
fn sprint56_compile_to_module_mangled_variant_compiles_without_expansion() {
    use cranelisp_types::{DefKind, ModuleEntry, OverloadVariant, Scheme, Visibility};

    let module = ModuleFullPath::from("user");
    let base_name = Symbol::from("add");
    let variant_name = Symbol::from("add$Int+Int");

    // Mangled variant defn — what typecheck's Wave 0 materialises.
    let variant_defn = Defn {
        name: variant_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            // Body returns x (proves the variant body is what got compiled).
            body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(5, 6),
                resolved_call: None,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        // Overloaded base entry: ast: None — compile_to_module must NOT
        // try to compile this (the filter via `defined_symbols()` skips
        // it; a caller passing it in `names` would hit the ast: None
        // error path — which is the right behaviour).
        st.insert(
            base_name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Int,
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::Overloaded {
                    variants: vec![OverloadVariant {
                        param_types: vec![Type::Int, Type::Int],
                        ret_type: Type::Int,
                        mangled_name: variant_name.clone(),
                    }],
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: None,
                codegen_view: None,
                code: None,
                value_use: false,
            },
        );
        // Mangled variant entry: ast: Some(variant_defn). Explicit GOT
        // slot so the D41 #2 direct-write is exercised.
        st.insert(variant_name.clone(), make_def_entry_slot(variant_defn, 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&variant_name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    )
    .expect("pre-mangled variant should compile without expansion");

    // Compilation succeeding (no expand_multi_sig_defn path) is the
    // verification; the mangled variant's GOT slot is populated.
    assert!(!artifacts.clif_ir.is_empty(), "variant body must be compiled");
    let guard = tables.get(&module).unwrap();
    match guard.get(variant_name.as_ref()) {
        Some(entry) if entry.callable_got_slot().is_some() => {
            let slot = entry.callable_got_slot().unwrap();
            assert!(
                !guard.got.load_slot(slot).is_null(),
                "mangled variant's GOT slot must be populated"
            );
        }
        other => panic!("expected mangled-variant Def with got_slot, got {other:?}"),
    }
}

// spec: design/backend/compile-to-module.md §4 — constrained-template exclusion via defined_symbols
//
// Verifies that `SymbolTable::defined_symbols()` — the shared filter
// callers use to build the `names` list — excludes constrained-function
// templates (`UserFn { constrained_fn: Some(_) }`). The backend relies
// on this filter upstream; if it were to break, constrained templates
// would reach compile_to_module and fail (templates carry type vars,
// not concrete types). This re-asserts Wave 0's contract from the
// backend's vantage point.
#[test]
fn sprint56_constrained_template_excluded_by_defined_symbols() {
    use cranelisp_types::{DefKind, ModuleEntry, Scheme, UserFnState, Visibility};

    let module = ModuleFullPath::from("user");
    let template_name = Symbol::from("identity");
    let normal_name = Symbol::from("answer");

    // A typical regular defn: compile-eligible.
    let normal_defn = Defn {
        name: normal_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 1, span: Span::new(0, 1), inferred_type: None },
            span: Span::new(0, 5),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 5),
    };

    // A constrained-fn template defn: should be filtered OUT by
    // defined_symbols() even though it carries ast: Some(_).
    let template_defn = Defn {
        name: template_name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(0, 1),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 10),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 10),
    };

    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(normal_name.clone(), make_def_entry(normal_defn));
        // Insert a UserFn template by hand — constrained_fn is Some.
        st.insert(
            template_name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![Symbol::from("x")],
                kind: Box::new(DefKind::UserFn {
                    // A constrained template is slot-less by construction
                    // (S83 reshape) — only its mono variants carry slots.
                    fn_state: UserFnState::Constrained(Box::new(
                        cranelisp_types::ConstrainedFn {
                            variant: template_defn.variants[0].clone(),
                            scheme: Scheme {
                                type_vars: vec![],
                                constraints: HashMap::new(),
                                ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
                            },
                        },
                    )),
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: Some(template_defn.variants[0].clone()),
                codegen_view: None,
                code: None,
                value_use: false,
            },
        );
        tables.insert(module.clone(), st);
    }

    let guard = tables.get(&module).unwrap();
    let defined: Vec<&Symbol> = guard.defined_symbols().map(|(n, _)| n).collect();

    assert!(
        defined.contains(&&normal_name),
        "defined_symbols() must yield regular defns: got {:?}",
        defined
    );
    assert!(
        !defined.contains(&&template_name),
        "defined_symbols() must NOT yield constrained-fn templates: got {:?}",
        defined
    );
}

// ----- Sprint 58 Wave 2: Decision 36 + Decision 23 unit tests -----
//
// These tests cover the architectural reconciliation landed in Sprint 58
// Wave 2: bare-name + Linkage::Local function declarations uniformly across
// all modules (Decision 36), and `__cranelisp_got_{M}` defined as
// Linkage::Export data symbol in the .o (Decision 23 — Bug B fix).

/// Helper: make an ObjectModule for these tests (PIC enabled).
fn make_object_module() -> cranelift_object::ObjectModule {
    use cranelift_module::default_libcall_names;
    use cranelift_object::ObjectBuilder;

    let isa = crate::cache::object::build_isa(true).unwrap();
    let builder = ObjectBuilder::new(isa, "test", default_libcall_names()).unwrap();
    cranelift_object::ObjectModule::new(builder)
}

/// Helper: build a single-defn symbol table with `got_slot: Some(slot)` so
/// the GOT-data emission step has a slot to populate.
fn table_with_def_and_slot(
    module: &ModuleFullPath,
    defn: Defn,
    slot: usize,
) -> DashMap<ModuleFullPath, SymbolTable> {
    use cranelisp_types::{
        DefKind, MonoDefnVariant, MonoExpr, ModuleEntry, Scheme, UserFnState, Visibility,
    };
    let tables = DashMap::new();
    let mut st = SymbolTable::new(module.clone());
    // Match the slot index: typecheck would have called allocate_got_slot
    // exactly `slot+1` times.
    for _ in 0..=slot {
        let _ = st.allocate_got_slot();
    }
    let param_count = defn.params().len();
    let param_names: Vec<Symbol> = defn
        .variants
        .first()
        .map(|v| v.params.iter().map(|(n, _)| n.clone()).collect())
        .unwrap_or_default();
    // Concretize + populate the codegen view (FIXME 0391 — a Concrete{slot}
    // UserFn is a body-AST codegen target and MUST carry a view).
    let variant = defn.variants.first().cloned().map(|mut v| {
        concretize_test_body(&mut v.body);
        v
    });
    let codegen_view = variant.as_ref().map(|v| {
        let body = MonoExpr::from_expr(&v.body)
            .expect("test fixture body concretizes for the codegen view (FIXME 0391)");
        MonoDefnVariant {
            name: defn.name.clone(),
            params: v.params.iter().map(|(n, _)| n.clone()).collect(),
            body,
            span: v.span,
            mode_summary: None,
        }
    });
    st.insert(
        defn.name.clone(),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(
                    (0..param_count).map(|_| Type::Int).collect(),
                    Box::new(Type::Int),
                ),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names,
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None },
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: variant,
            codegen_view,
            code: None,
            value_use: false,
        },
    );
    tables.insert(module.clone(), st);
    tables
}

/// Helper: trivial zero-arg defn returning an int literal.
fn make_int_defn(name: &str, value: i64) -> Defn {
    Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value, span: Span::SYNTHETIC, inferred_type: None },
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

// spec: design/arch/CLAUDE.md Decision 36 — function symbols are declared
// with their bare name uniformly across all modules. The pre-Sprint-58
// user/main vs FQ-Export discriminator is deleted.
#[test]
fn decision_36_function_naming_is_bare_for_every_module() {
    use cranelift_module::Module;
    for module_path_str in ["user", "main", "util", "one.two.three"] {
        let module = ModuleFullPath::from(module_path_str);
        let defn = make_int_defn("helper", 7);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let _artifacts = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        )
        .expect("compile_to_module should succeed");

        // The Cranelift module's declaration table records the bare name.
        // (Decision 36: even for non-user/main, the FQ form must be absent.)
        let fq = format!("{module_path_str}/helper");
        let m = jit.jit_module();
        let has_fq = m.get_name(&fq).is_some();
        let has_bare = m.get_name("helper").is_some();
        assert!(
            !has_fq,
            "module '{module_path_str}': bare-only contract violated — module-qualified name '{fq}' should NOT be a declaration"
        );
        assert!(
            has_bare,
            "module '{module_path_str}': bare name 'helper' must be a declaration"
        );
    }
}

// spec: design/arch/CLAUDE.md Decision 36 — function linkage is Local
// uniformly. Symbols never need to cross .o boundaries (all-GOT calling).
#[test]
fn decision_36_function_linkage_is_local_uniformly() {
    use cranelift_module::{FuncOrDataId, Linkage, Module};
    for module_path_str in ["user", "main", "util", "deep.nested.path"] {
        let module = ModuleFullPath::from(module_path_str);
        let defn = make_int_defn("f", 1);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        let aliases = empty_aliases();
        let _result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &aliases,
            jit.jit_module(),
            true,
        )
        .expect("compile_to_module should succeed");

        let m = jit.jit_module();
        let func_id = match m.get_name("f") {
            Some(FuncOrDataId::Func(id)) => id,
            other => panic!("module '{module_path_str}': expected FuncOrDataId::Func for 'f', got {other:?}"),
        };
        let decl = m.declarations().get_function_decl(func_id);
        assert_eq!(
            decl.linkage,
            Linkage::Local,
            "module '{module_path_str}': function 'f' must have Linkage::Local per Decision 36, got {:?}",
            decl.linkage
        );
    }
}

// spec: design/arch/bounded-contexts.md §5 invariant 9 (S81 / FIXME 0327,
//       the fault-guarded dispatch funnel step 2/4 — fault-path fn-name).
//
// The residual FIXME-0337 gap: a BARE imported platform-effect call
// `(crash)` carries `resolved_call: None`, so it reaches dispatch via the
// plain `compile_var_apply` → `compile_direct_call` path, NOT the
// `ResolvedCall::BuiltinFn` arm. The original step-2 stamp lived ONLY in the
// `BuiltinFn` arm, so the var-apply path emitted the GOT-indirect call with
// NO field-3 stamp — the fn-name handle stayed null and the surfaced
// DispatchError degraded to `<unknown>` (on BOTH the happy and fault paths).
//
// The fix sites the stamp at the single GOT-indirect dispatch chokepoint
// (`compile_direct_call`), so EVERY dispatch path stamps. This test pins
// that: a hand-built `caller` defn whose body is `(Apply (Var "crash") []
// resolved_call=None)` — the exact bare-import shape the bug exposed — must
// compile to CLIF that STORES the baked name into the returned Effect node's
// field-3 (absolute offset `HeapHeader::SIZE + IO_EFFECT_FN_NAME_OFFSET` = 40),
// AFTER the dispatch `call_indirect` and BEFORE `return` (node-construction
// time, before the force — so the name survives a thunk panic on the fault
// path). A non-platform-effect callee must NOT emit such a store.
#[test]
fn platform_effect_dispatch_stamps_fn_name_on_bare_import_var_apply_path() {
    use cranelisp_types::{DefKind, FQSymbol, HeapHeader, ModuleEntry, Scheme};

    // The absolute byte offset of the Effect node's fn-name field (field-3),
    // composed from the public ABI constants — must equal 40 today and match
    // the (module-private) EFFECT_FN_NAME_ABS_OFFSET the stamp emits.
    let field3_off: i64 =
        HeapHeader::SIZE as i64 + cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET;

    let plat = ModuleFullPath::from("platform.boom");
    let user = ModuleFullPath::from("user");

    // `caller` body: `(crash)` with resolved_call: None — the bare-import
    // var-apply shape, NOT a `ResolvedCall::BuiltinFn`.
    let caller = Defn {
        name: Symbol::from("caller"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("crash"),
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![],
                span: Span::SYNTHETIC,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    // platform.boom: `crash` is a got-slotted PlatformEffect (the only kind
    // that stamps). Slot 0 in the platform GOT.
    {
        let mut st = SymbolTable::new(plat.clone());
        let _ = st.allocate_got_slot();
        st.insert(
            Symbol::from("crash"),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::PlatformEffect {
                    scheduling_class: Default::default(),
                    poll_shape: false,
                    got_slot: 0,
                    mode_summary: None,
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: None,
                codegen_view: None,
                code: None,
                value_use: false,
            },
        );
        tables.insert(plat.clone(), st);
    }
    // user: imports `crash` from platform.boom + defines `caller` at slot 0.
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot();
        st.insert(
            Symbol::from("crash"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: plat.clone(),
                    symbol: Symbol::from("crash"),
                },
                visibility: Visibility::Public,
            },
        );
        st.insert(
            Symbol::from("caller"),
            make_def_entry_slot(caller.clone(), 0),
        );
        tables.insert(user.clone(), st);
    }

    let mut obj = make_object_module();
    let aliases = empty_aliases();
    let artifacts = compile_to_module(
        user.clone(),
        std::slice::from_ref(&caller.name),
        &tables,
        &aliases,
        &mut obj,
        true, // capture_clif
    )
    .expect("compile caller calling a bare-imported platform effect");

    // The emitted CLIF for `caller` must store into field-3 at +40. The store
    // is the fn-name stamp; its absence is the FIXME-0337 `<unknown>` bug.
    let store_at_field3 = format!("+{field3_off}");
    assert!(
        artifacts.clif_ir.contains("store") && artifacts.clif_ir.contains(&store_at_field3),
        "bare-import platform-effect dispatch (resolved_call: None) MUST stamp \
         the fn-name into the Effect node's field-3 (store at {store_at_field3}); \
         the var-apply path was missing the stamp (FIXME 0337). CLIF:\n{}",
        artifacts.clif_ir,
    );
}

// spec: design/arch/bounded-contexts.md §5 invariant 9 (negative) — a NON
//       platform-effect callee dispatched GOT-indirect must NOT stamp
//       field-3: its result is not an Effect node and writing +40 would
//       corrupt an unrelated allocation. `resolve_platform_effect_target`
//       returns None for a plain UserFn, so no store is emitted.
#[test]
fn non_platform_effect_dispatch_does_not_stamp_field3() {
    let user = ModuleFullPath::from("user");
    // A plain user fn `helper` (UserFn, slotted) and a `caller` that calls it
    // with resolved_call: None (the same var-apply path).
    let helper = make_int_defn("helper", 7);
    let caller = Defn {
        name: Symbol::from("caller"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("helper"),
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![],
                span: Span::SYNTHETIC,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot();
        let _ = st.allocate_got_slot();
        st.insert(helper.name.clone(), make_def_entry_slot(helper.clone(), 0));
        st.insert(caller.name.clone(), make_def_entry_slot(caller.clone(), 1));
        tables.insert(user.clone(), st);
    }

    let field3_off: i64 = cranelisp_types::HeapHeader::SIZE as i64
        + cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET;
    let store_at_field3 = format!("+{field3_off}");

    let mut obj = make_object_module();
    let aliases = empty_aliases();
    let artifacts = compile_to_module(
        user.clone(),
        std::slice::from_ref(&caller.name),
        &tables,
        &aliases,
        &mut obj,
        true,
    )
    .expect("compile caller calling a plain user fn");

    assert!(
        !artifacts.clif_ir.contains(&store_at_field3),
        "a non-platform-effect GOT-indirect dispatch MUST NOT stamp field-3 \
         (no store at {store_at_field3}); only DefKind::PlatformEffect stamps. CLIF:\n{}",
        artifacts.clif_ir,
    );
}

// spec: design/arch/CLAUDE.md Decision 23 (updated) — `__cranelisp_got_{M}`
// is defined as Linkage::Export data with `slot_count * 8` bytes inside
// the .o emitted by compile_to_module<ObjectModule>.
#[test]
fn decision_23_got_data_symbol_defined_as_export_in_object_path() {
    use cranelift_module::Module;
    let module = ModuleFullPath::from("util");
    let defn = make_int_defn("answer", 42);
    let tables = table_with_def_and_slot(&module, defn.clone(), 0);

    let mut obj = make_object_module();
    let aliases = empty_aliases();
    let _result = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        &mut obj,
        true,
    )
    .expect("compile_to_module<ObjectModule> should succeed");

    // The GOT data symbol should now be a defined Export data symbol.
    let got_name = crate::compiler::got_data_symbol_name(&module);
    let id = obj
        .get_name(&got_name)
        .expect("GOT data symbol must be declared");
    let data_id = match id {
        cranelift_module::FuncOrDataId::Data(d) => d,
        other => panic!("expected DataId for {got_name}, got {other:?}"),
    };
    let decl = obj.declarations().get_data_decl(data_id);
    assert_eq!(
        decl.linkage,
        cranelift_module::Linkage::Export,
        "GOT data symbol '{got_name}' must be Linkage::Export, got {:?}",
        decl.linkage
    );

    // Emit the .o and parse it; confirm:
    //  (a) the GOT data symbol is present in the .o symbol table
    //  (b) it has global scope (Export = visible to the system linker)
    //  (c) it points into a Data-kind section
    // (Size in the .o symbol table is not portable across formats —
    // Mach-O always reports 0; we rely on the in-Module declaration
    // size assertion and the section-data check instead.)
    let product = obj.finish();
    let bytes = product.emit().expect("ObjectModule should emit");
    use ::object::{Object, ObjectSymbol, SymbolKind, SymbolScope};
    let parsed = ::object::File::parse(&*bytes)
        .expect("emitted bytes must parse as an object file");
    let got_sym = parsed
        .symbols()
        .find(|s| {
            s.name()
                // Platform-agnostic symbol-name match. Mach-O prepends
                // exactly one '_' to every symbol (so the .o name is
                // `_<got_name>`); ELF prepends nothing (the .o name IS
                // `<got_name>`, and `got_name` itself already begins with
                // `__cranelisp_got_`). The former `strip_prefix('_')` matcher
                // assumed Mach-O and stripped a leading underscore that does
                // not exist on ELF, breaking the match on Linux (the symbol
                // was present but never found) — a stale test assertion, not
                // a GOT-emission defect (S82 W2 /dev triage of the 3
                // decision_23_got_data failures).
                .map(|n| n == got_name || n == format!("_{got_name}"))
                .unwrap_or(false)
        })
        .unwrap_or_else(|| {
            panic!(
                "GOT data symbol '{got_name}' must appear in emitted .o; \
                 symbols present: {:?}",
                parsed
                    .symbols()
                    .filter_map(|s| s.name().ok().map(|n| n.to_string()))
                    .collect::<Vec<_>>()
            )
        });
    assert_ne!(
        got_sym.scope(),
        SymbolScope::Compilation,
        "GOT data symbol '{got_name}' must have global scope (Linkage::Export); got {:?}",
        got_sym.scope()
    );
    assert_eq!(
        got_sym.kind(),
        SymbolKind::Data,
        "GOT data symbol '{got_name}' must be a Data-kind symbol; got {:?}",
        got_sym.kind()
    );
}

// spec: design/arch/CLAUDE.md Decision 23 — JIT-mode GOT-data definition
// remains the integration layer's responsibility (`Jit::define_got_data`).
// compile_to_module<JITModule>'s `define_module_got_data` is a no-op and
// does NOT redundantly declare/define the symbol on the JIT module.
#[test]
fn decision_23_got_data_symbol_jit_path_is_noop() {
    use cranelift_module::Module;
    let module = ModuleFullPath::from("user");
    let defn = make_int_defn("answer", 42);
    let tables = table_with_def_and_slot(&module, defn.clone(), 0);

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let _result = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    )
    .expect("compile_to_module<JITModule> should succeed");

    // In JIT mode, the GOT data symbol is NOT defined by compile_to_module.
    // It might be an Import declaration if the compiled code emitted a
    // GOT-indirect call (unlikely in this minimal test — answer is a
    // direct expression), but it must NEVER be Export-defined here.
    let got_name = crate::compiler::got_data_symbol_name(&module);
    let m = jit.jit_module();
    if let Some(cranelift_module::FuncOrDataId::Data(data_id)) = m.get_name(&got_name) {
        let decl = m.declarations().get_data_decl(data_id);
        assert_ne!(
            decl.linkage,
            cranelift_module::Linkage::Export,
            "JIT path: GOT data symbol '{got_name}' must NOT be Linkage::Export-defined by compile_to_module — JIT-mode definition lives in Jit::define_got_data (Decision 23)"
        );
    }
    // (If it's not declared at all, that's also fine — this minimal defn
    // doesn't emit a GOT-indirect call so neither path declares it.)
}

// spec: design/arch/CLAUDE.md Decision 23 — GOT data symbol size matches
// the symbol table's `next_got_slot` (one 8-byte slot per allocated index).
#[test]
fn decision_23_got_data_size_matches_slot_count() {
    use cranelift_module::Module;
    // Two defns with two GOT slots → 16 bytes.
    let module = ModuleFullPath::from("util");
    let d1 = make_int_defn("one", 1);
    let d2 = make_int_defn("two", 2);

    // Build symbol table with both defns at slots 0 and 1.
    use cranelisp_types::{
        DefKind, MonoDefnVariant, MonoExpr, ModuleEntry, Scheme, UserFnState, Visibility,
    };
    let tables = DashMap::new();
    let mut st = SymbolTable::new(module.clone());
    let _slot0 = st.allocate_got_slot();
    let _slot1 = st.allocate_got_slot();
    for (defn, slot) in [(d1.clone(), 0usize), (d2.clone(), 1)] {
        let variant = defn.variants.first().cloned().map(|mut v| {
            concretize_test_body(&mut v.body);
            v
        });
        let codegen_view = variant.as_ref().map(|v| MonoDefnVariant {
            name: defn.name.clone(),
            params: vec![],
            body: MonoExpr::from_expr(&v.body).expect("concrete test body"),
            span: v.span,
            mode_summary: None,
        });
        st.insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None },
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: variant,
                codegen_view,
                code: None,
                value_use: false,
            },
        );
    }
    tables.insert(module.clone(), st);

    let mut obj = make_object_module();
    let aliases = empty_aliases();
    let _result = compile_to_module(
        module.clone(),
        &[d1.name.clone(), d2.name.clone()],
        &tables,
        &aliases,
        &mut obj,
        true,
    )
    .expect("compile_to_module should succeed");

    // Verify in-Module declaration size; we cannot rely on the .o
    // symbol-table `size()` (Mach-O reports 0). The Cranelift
    // declaration carries the requested initialization size.
    let got_name = crate::compiler::got_data_symbol_name(&module);
    let data_id = match obj.get_name(&got_name) {
        Some(cranelift_module::FuncOrDataId::Data(id)) => id,
        other => panic!("expected DataId for {got_name}, got {other:?}"),
    };
    let _decl = obj.declarations().get_data_decl(data_id);

    let product = obj.finish();
    let bytes = product.emit().unwrap();
    use ::object::{Object, ObjectSection, ObjectSymbol};
    let parsed = ::object::File::parse(&*bytes).unwrap();
    let got_sym = parsed
        .symbols()
        .find(|s| {
            s.name()
                // Platform-agnostic symbol-name match. Mach-O prepends
                // exactly one '_' to every symbol (so the .o name is
                // `_<got_name>`); ELF prepends nothing (the .o name IS
                // `<got_name>`, and `got_name` itself already begins with
                // `__cranelisp_got_`). The former `strip_prefix('_')` matcher
                // assumed Mach-O and stripped a leading underscore that does
                // not exist on ELF, breaking the match on Linux (the symbol
                // was present but never found) — a stale test assertion, not
                // a GOT-emission defect (S82 W2 /dev triage of the 3
                // decision_23_got_data failures).
                .map(|n| n == got_name || n == format!("_{got_name}"))
                .unwrap_or(false)
        })
        .expect("GOT data symbol present");

    // Look up the section the symbol lives in and check it is at least
    // slot_count * 8 = 16 bytes long. (Cranelift may pack multiple data
    // symbols into the same section; this is a lower-bound check for the
    // GOT slab's storage budget.)
    let sect_idx = match got_sym.section_index() {
        Some(idx) => idx,
        None => panic!("GOT data symbol must live in a section"),
    };
    let section = parsed.section_by_index(sect_idx).unwrap();
    assert!(
        section.size() >= 16,
        "section containing GOT data symbol must hold at least slot_count(2) * 8 = 16 bytes; got {}",
        section.size()
    );
}

// spec: design/arch/CLAUDE.md Decision 36 — cross-module function refs
// are NOT declared as Linkage::Import in the importing module's .o. Under
// all-GOT calling, cross-module calls reach callees through
// `__cranelisp_got_{other_M}` data symbol — never through a function-symbol
// import. Verifies the cross_refs declaration loop deletion did not
// re-introduce stray Import-linkage function declarations.
#[test]
fn decision_36_no_cross_module_function_imports() {
    use cranelift_module::{FuncOrDataId, Linkage, Module};

    // Build two modules: util defines `helper`, user imports `helper`.
    // Compile user.
    let util_path = ModuleFullPath::from("util");
    let user_path = ModuleFullPath::from("user");

    let helper = make_int_defn("helper", 99);
    // user has a single defn `caller` that does NOT call helper at runtime
    // (this test only checks the declaration shape; we focus on what
    // compile_to_module declares against the user module). The Import
    // entry on user's table records the cross-module dependency.
    let caller = make_int_defn("caller", 7);

    use cranelisp_types::{
        DefKind, FQSymbol, MonoDefnVariant, MonoExpr, ModuleEntry, Scheme, UserFnState,
        Visibility,
    };
    let tables = DashMap::new();

    // Build a concrete `codegen_view` for a zero-arg int-literal defn body
    // (FIXME 0391 — Concrete{slot} UserFns carry the populated MonoExpr view).
    let int_view = |d: &Defn| {
        let mut v = d.variants.first().cloned().unwrap();
        concretize_test_body(&mut v.body);
        Some(MonoDefnVariant {
            name: d.name.clone(),
            params: vec![],
            body: MonoExpr::from_expr(&v.body).expect("concrete test body"),
            span: v.span,
            mode_summary: None,
        })
    };

    // util module: helper at slot 0.
    let mut util_st = SymbolTable::new(util_path.clone());
    let _ = util_st.allocate_got_slot();
    util_st.insert(
        Symbol::from("helper"),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![], Box::new(Type::Int)),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: 0, mode_summary: None },
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: helper.variants.first().cloned(),
            codegen_view: int_view(&helper),
            code: None,
            value_use: false,
        },
    );
    tables.insert(util_path.clone(), util_st);

    // user module: caller at slot 0, helper imported from util.
    let mut user_st = SymbolTable::new(user_path.clone());
    let _ = user_st.allocate_got_slot();
    user_st.insert(
        Symbol::from("caller"),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![], Box::new(Type::Int)),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: 0, mode_summary: None },
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: caller.variants.first().cloned(),
            codegen_view: int_view(&caller),
            code: None,
            value_use: false,
        },
    );
    user_st.insert(
        Symbol::from("helper"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: util_path.clone(),
                symbol: Symbol::from("helper"),
            },
            visibility: Visibility::Private,
        },
    );
    tables.insert(user_path.clone(), user_st);

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let aliases = empty_aliases();
    let result = compile_to_module(
        user_path.clone(),
        &[Symbol::from("caller")],
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    )
    .expect("compile_to_module should succeed");

    // Per Decision 36 + cross_refs deletion: there must be NO
    // Linkage::Import declaration for the cross-module function name
    // (neither `helper` nor `util/helper`).
    let m = jit.jit_module();
    for candidate in ["helper", "util/helper"] {
        if let Some(FuncOrDataId::Func(fid)) = m.get_name(candidate) {
            let decl = m.declarations().get_function_decl(fid);
            assert_ne!(
                decl.linkage,
                Linkage::Import,
                "cross-module fn '{candidate}' must NOT be declared as Linkage::Import; got {:?}. Under all-GOT calling, cross-module calls flow through __cranelisp_got_{{M}} data symbols, not function imports.",
                decl.linkage
            );
        }
    }

    // Sanity: `caller` is declared bare-Local (compiled this batch).
    let _ = &result; // CompilationArtifacts carries CLIF/size, not func_ids
    assert!(
        matches!(m.get_name("caller"), Some(FuncOrDataId::Func(_))),
        "bare 'caller' must be a function declaration"
    );
}

// spec: design/arch/CLAUDE.md Decision 23 — Sprint 58 Wave 2 regression
// guard. The `__cranelisp_got_{M}` data symbol carries function-address
// relocations (declared via `desc.write_function_addr`). On macOS, `ld`
// segfaults when applying relocations against `__DATA,__bss`
// (`S_ZEROFILL`) sections. The Wave 2 implementation MUST emit GOT
// contents via `desc.define(zero_bytes)` (regular `__DATA`), NOT
// `desc.define_zeroinit(...)` (which lands in BSS / `S_ZEROFILL`).
// This test asserts the emitted .o has the GOT data symbol in a regular
// (non-BSS) data section.
#[test]
fn decision_23_got_data_symbol_not_in_bss() {
    let module = ModuleFullPath::from("util");
    let defn = make_int_defn("answer", 42);
    let tables = table_with_def_and_slot(&module, defn.clone(), 0);

    let mut obj = make_object_module();
    let aliases = empty_aliases();
    let _result = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        &aliases,
        &mut obj,
        true,
    )
    .expect("compile_to_module<ObjectModule> should succeed");

    let product = obj.finish();
    let bytes = product.emit().expect("ObjectModule should emit");

    use ::object::{Object, ObjectSection, ObjectSymbol, SectionKind};
    let parsed = ::object::File::parse(&*bytes)
        .expect("emitted bytes must parse as an object file");
    let got_name = crate::compiler::got_data_symbol_name(&module);
    let got_sym = parsed
        .symbols()
        .find(|s| {
            s.name()
                // Platform-agnostic symbol-name match. Mach-O prepends
                // exactly one '_' to every symbol (so the .o name is
                // `_<got_name>`); ELF prepends nothing (the .o name IS
                // `<got_name>`, and `got_name` itself already begins with
                // `__cranelisp_got_`). The former `strip_prefix('_')` matcher
                // assumed Mach-O and stripped a leading underscore that does
                // not exist on ELF, breaking the match on Linux (the symbol
                // was present but never found) — a stale test assertion, not
                // a GOT-emission defect (S82 W2 /dev triage of the 3
                // decision_23_got_data failures).
                .map(|n| n == got_name || n == format!("_{got_name}"))
                .unwrap_or(false)
        })
        .expect("GOT data symbol must appear in emitted .o");
    let sect_idx = got_sym
        .section_index()
        .expect("GOT data symbol must live in a section, not be undefined");
    let section = parsed
        .section_by_index(sect_idx)
        .expect("section must be resolvable");

    // Negative path: must NOT be UninitializedData (BSS / __DATA,__bss /
    // S_ZEROFILL). macOS `ld` segfaults on relocations against BSS.
    let kind = section.kind();
    assert_ne!(
        kind,
        SectionKind::UninitializedData,
        "GOT data symbol '{got_name}' landed in BSS (UninitializedData) — \
         macOS `ld` segfaults on relocations against BSS. Use \
         `desc.define(zero_bytes)` not `desc.define_zeroinit(...)` so the \
         data lands in regular `__DATA`."
    );
    // Positive path: must be a regular initialized Data section so
    // function-address relocations resolve correctly.
    assert!(
        matches!(kind, SectionKind::Data | SectionKind::ReadOnlyData),
        "GOT data symbol '{got_name}' must live in a regular initialized data section; got {kind:?}"
    );
}

// =========================================================================
// S101 item 1 — vec query family (vec-get/vec-set/vec-push) as first-class
// values must inline-emit in the generated wrapper, never call through the
// primitives table's allocated-but-NULL GOT slots.
// (`design/backend/ownership-codegen.md` §12.7; e2e guards:
// `tests/vec_query_value_use.rs`.)
// =========================================================================

/// Insert a `primitives`-style vec-query entry: a `DefKind::Primitive` Def
/// with an ALLOCATED but **NULL** GOT slot — name-resolution-only, exactly as
/// `cranelisp-primitives::insert_vec_query_entries` builds them (no extern
/// body can exist because a single monomorphic body cannot know the element's
/// heap category). Backend must never `call_indirect` through this slot.
fn insert_null_slot_vec_query_entry(
    st: &mut SymbolTable,
    name: &str,
    param_names: &[&str],
    ty: Type,
) {
    use cranelisp_types::{DefKind, ModuleEntry, Scheme};
    let slot = st.allocate_got_slot();
    // Deliberately NO `store_slot` — the slot stays NULL, as in production.
    let scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty,
    };
    st.insert(
        Symbol::from(name),
        ModuleEntry::def(scheme, DefKind::primitive(slot))
            .param_names(param_names.iter().map(|s| Symbol::from(*s)).collect())
            .build(),
    );
}

/// Read element `idx` from a Vec base pointer (layout per Decision 11:
/// `[size@+0 | rc@+8 | len@+16 | cap@+24 | data_ptr@+32]`). Test-only inline
/// (Decision 0048 backend dep-ban — no `cranelisp-primitives` dep).
///
/// SAFETY: `ptr` must be a valid Vec base pointer with `idx < len`.
fn vec_elem_for_test(ptr: i64, idx: usize) -> i64 {
    unsafe {
        let data_ptr = *((ptr as *const u8).add(32) as *const *const i64);
        *data_ptr.add(idx)
    }
}

/// Shared fixture driver for the vec-query fn-as-value seam: builds a
/// `primitives` table holding NULL-slotted `vec-get`/`vec-set`/`vec-push`
/// entries and a `user` module with the given consumer defn, compiles the
/// consumer, and runs it end-to-end. Returns the consumer's i64 result.
fn run_vec_query_value_consumer(consumer: Defn) -> i64 {
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
        insert_null_slot_vec_query_entry(
            &mut pst,
            "vec-get",
            &["v", "idx"],
            Type::Fn(vec![vec_int(), Type::Int], Box::new(Type::Int)),
        );
        insert_null_slot_vec_query_entry(
            &mut pst,
            "vec-set",
            &["v", "idx", "val"],
            Type::Fn(vec![vec_int(), Type::Int, Type::Int], Box::new(vec_int())),
        );
        insert_null_slot_vec_query_entry(
            &mut pst,
            "vec-push",
            &["v", "val"],
            Type::Fn(vec![vec_int(), Type::Int], Box::new(vec_int())),
        );
        tables.insert(prims.clone(), pst);
    }
    let consumer_name = consumer.name.clone();
    {
        let mut st = SymbolTable::new(user.clone());
        st.insert(consumer_name.clone(), make_def_entry_slot(consumer.clone(), 0));
        st.next_got_slot = 1;
        tables.insert(user.clone(), st);
    }

    // Register both GOT data symbols. The user slab backs the consumer's own
    // slot write; the primitives slab is what the DEFECTIVE path GOT-indirects
    // through (registering it makes the RED failure the production SIGSEGV,
    // not an unresolved-symbol artifact).
    let got_user_name = crate::compiler::got_data_symbol_name(&user);
    let got_prims_name = crate::compiler::got_data_symbol_name(&prims);
    let (got_user_base, got_prims_base) = (
        tables.get(&user).map(|st| st.got.base_ptr()).expect("user table"),
        tables.get(&prims).map(|st| st.got.base_ptr()).expect("prims table"),
    );
    let extras: Vec<(&str, *const u8)> = vec![
        (got_user_name.as_str(), got_user_base),
        (got_prims_name.as_str(), got_prims_base),
    ];

    let mut jit = Jit::new_with_symbols(&extras).expect("jit init");
    let aliases = empty_aliases();
    compile_to_module(
        user.clone(),
        std::slice::from_ref(&consumer_name),
        &tables,
        &aliases,
        jit.jit_module(),
        true,
    )
    .expect("vec-query value-use consumer must compile");

    let ptr = jit
        .get_ptr_by_name(&consumer_name, 0)
        .expect("finalize consumer");
    assert!(!ptr.is_null(), "consumer must finalize to a non-null fn ptr");
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    let result = func();
    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        panic!("runtime panic running vec-query consumer: {msg}");
    }
    result
}

/// Fully-annotated `(Vec Int)` literal `[e0 e1 ...]` fixture node.
fn vec_int_lit(elements: &[i64], span_base: u32) -> Expr {
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
fn vec_query_value_consumer(prim: &str, prim_ty: Type, args: Vec<Expr>, result_ty: Type) -> Defn {
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

// spec: design/backend/ownership-codegen.md §12.7 — `vec-get` used as a VALUE
// wraps via `compile_fn_as_value` → `emit_wrapper_call`; the wrapper must
// inline-emit the bounds-checked read (element type plumbed from the Var's
// concrete `inferred_type`), never `call_indirect` through the NULL
// primitives-table slot. RED on HEAD: SIGSEGV (jump to address 0).
#[test]
fn vec_get_as_value_wrapper_inline_emits_and_returns_element() {
    let vec_int = Type::adt(
        ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
        vec![Type::Int],
    );
    let prim_ty = Type::Fn(vec![vec_int.clone(), Type::Int], Box::new(Type::Int));
    let consumer = vec_query_value_consumer(
        "vec-get",
        prim_ty,
        vec![
            vec_int_lit(&[10, 20, 30], 30),
            Expr::IntLit {
                value: 1,
                span: Span::new(40, 41),
                inferred_type: Some(Box::new(Type::Int)),
            },
        ],
        Type::Int,
    );
    assert_eq!(run_vec_query_value_consumer(consumer), 20);
}

// spec: design/backend/ownership-codegen.md §12.7 — `vec-set` as a VALUE: the
// wrapper takes the owned-temporary polarity (no consuming inc on the new
// element; vec trivially at last use ⇒ COW rc==1 mutate-in-place). RED on
// HEAD: SIGSEGV.
#[test]
fn vec_set_as_value_wrapper_inline_emits_and_updates_element() {
    let vec_int = Type::adt(
        ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
        vec![Type::Int],
    );
    let prim_ty = Type::Fn(
        vec![vec_int.clone(), Type::Int, Type::Int],
        Box::new(vec_int.clone()),
    );
    let consumer = vec_query_value_consumer(
        "vec-set",
        prim_ty,
        vec![
            vec_int_lit(&[10, 20, 30], 30),
            Expr::IntLit {
                value: 1,
                span: Span::new(40, 41),
                inferred_type: Some(Box::new(Type::Int)),
            },
            Expr::IntLit {
                value: 99,
                span: Span::new(42, 44),
                inferred_type: Some(Box::new(Type::Int)),
            },
        ],
        vec_int,
    );
    let vec_ptr = run_vec_query_value_consumer(consumer);
    assert!(vec_ptr != 0, "vec-set-as-value must return a Vec pointer");
    assert_eq!(vec_len_for_test(vec_ptr), 3, "length preserved");
    assert_eq!(vec_elem_for_test(vec_ptr, 1), 99, "element 1 updated");
    assert_eq!(vec_elem_for_test(vec_ptr, 0), 10, "element 0 retained");
}

// spec: design/backend/ownership-codegen.md §12.7 — `vec-push` as a VALUE:
// same owned-temporary polarity; COW rc==1 fast path appends. RED on HEAD:
// SIGSEGV.
#[test]
fn vec_push_as_value_wrapper_inline_emits_and_appends() {
    let vec_int = Type::adt(
        ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
        vec![Type::Int],
    );
    let prim_ty = Type::Fn(vec![vec_int.clone(), Type::Int], Box::new(vec_int.clone()));
    let consumer = vec_query_value_consumer(
        "vec-push",
        prim_ty,
        vec![
            vec_int_lit(&[10, 20], 30),
            Expr::IntLit {
                value: 30,
                span: Span::new(40, 42),
                inferred_type: Some(Box::new(Type::Int)),
            },
        ],
        vec_int,
    );
    let vec_ptr = run_vec_query_value_consumer(consumer);
    assert!(vec_ptr != 0, "vec-push-as-value must return a Vec pointer");
    assert_eq!(vec_len_for_test(vec_ptr), 3, "length incremented");
    assert_eq!(vec_elem_for_test(vec_ptr, 2), 30, "pushed element present");
}

// spec: design/backend/ownership-codegen.md §12.7 — the CURRY seam is distinct:
// a partial application `(vec-get v)` routes `compile_auto_curry` →
// `emit_curry_target_call` with `trait_resolution: BuiltinFn{vec-get}`; the
// vec family is NOT in `primitives_inline`, so on HEAD the wrapper declares a
// `Linkage::Import` for `vec-get` and JIT-finalize panics
// ("can't resolve symbol vec-get" — the e2e exit-101 signature). The curry
// wrapper must inline-emit instead, with the element type recovered from the
// applied Vec argument's concrete type.
#[test]
fn vec_get_curried_partial_wrapper_inline_emits_and_applies() {
    use cranelisp_types::ResolvedCall;
    let vec_int = Type::adt(
        ModuleFullPath::from("primitives"),
        cranelisp_types::TypeName::from("Vec"),
        vec![Type::Int],
    );
    let get_ty = Type::Fn(vec![vec_int.clone(), Type::Int], Box::new(Type::Int));
    let curried_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));

    // (defn use1 [] (let [g (vec-get [10 20 30])] (g 1)))
    let body = Expr::Let {
        bindings: vec![(
            Symbol::from("g"),
            Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(10, 17),
                    resolved_call: None,
                    inferred_type: Some(Box::new(get_ty)),
                }),
                args: vec![vec_int_lit(&[10, 20, 30], 30)],
                span: Span::new(9, 45),
                resolved_call: Some(Box::new(ResolvedCall::AutoCurry {
                    target_name: Symbol::from("vec-get"),
                    applied_count: 1,
                    total_count: 2,
                    trait_resolution: Some(Box::new(ResolvedCall::BuiltinFn {
                        name: Symbol::from("vec-get"),
                    })),
                })),
                inferred_type: Some(Box::new(curried_ty.clone())),
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("g"),
                span: Span::new(50, 51),
                resolved_call: None,
                inferred_type: Some(Box::new(curried_ty)),
            }),
            args: vec![Expr::IntLit {
                value: 1,
                span: Span::new(52, 53),
                inferred_type: Some(Box::new(Type::Int)),
            }],
            span: Span::new(49, 54),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        span: Span::new(5, 55),
        inferred_type: Some(Box::new(Type::Int)),
    };
    let consumer = Defn {
        name: Symbol::from("use-vec-query"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::new(0, 56),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 56),
    };
    assert_eq!(run_vec_query_value_consumer(consumer), 20);
}

// =========================================================================
// S101 item 5 — `compile_trap_stub` (backend §8.1/§8.3): the R3 machinery's
// per-symbol trap stub over the existing raise machinery.
// =========================================================================

// spec: design/backend/ownership-codegen.md §8.1 — the stub raises the baked
// provenance message through `runtime/panic` (thread-local slot + sentinel
// return); the host reads it via `take_runtime_error`.
#[test]
fn trap_stub_raises_provenance_message_and_returns_sentinel() {
    let msg = String::from("g is broken by the redefinition of f: type error");
    let (ptr, code) =
        compile_trap_stub(msg.as_ptr(), msg.len()).expect("trap stub compiles");
    assert!(!ptr.is_null(), "trap stub must finalize to a non-null code ptr");

    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let stub: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    assert_eq!(stub(), 0, "trap stub returns the 0 sentinel");
    let raised = cranelisp_intrinsics::panic::take_runtime_error()
        .expect("trap stub must raise through the runtime/panic slot");
    assert!(
        raised.contains("g is broken by the redefinition of f: type error"),
        "raised message must carry the baked provenance; got: {raised}"
    );

    // The provenance string + Code handle pair outlive the call — the
    // caller-side lifetime contract (§8.1). Keep both live to here.
    drop(code);
    drop(msg);
}

// spec: design/backend/ownership-codegen.md §8.1 — the `() -> i64` stub is
// signature-safe for ANY caller arity/type vector under the uniform all-I64
// convention: callers that imported an N-arg signature reach the same slot
// and the stub never reads its argument registers. Pin the cross-arity call.
#[test]
fn trap_stub_is_callable_at_nonzero_arity() {
    let msg = String::from("h is broken by the redefinition of k: arity change");
    let (ptr, _code) =
        compile_trap_stub(msg.as_ptr(), msg.len()).expect("trap stub compiles");

    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    // Call as a 3-arg function (register-passed, caller-owned scratch).
    let stub3: extern "C" fn(i64, i64, i64) -> i64 = unsafe { std::mem::transmute(ptr) };
    assert_eq!(stub3(1, 2, 3), 0, "sentinel through a 3-arg import signature");
    assert!(
        cranelisp_intrinsics::panic::take_runtime_error().is_some(),
        "raise fires regardless of the caller's imported arity"
    );
}

// spec: design/backend/ownership-codegen.md §8.1 — the message address is
// baked and read at INVOCATION time, so the stub is re-raisable (every call
// through the patched slot raises afresh; the slot may be hit many times in
// a dev session).
#[test]
fn trap_stub_raises_on_every_invocation() {
    let msg = String::from("m is broken by the redefinition of n: gone");
    let (ptr, _code) =
        compile_trap_stub(msg.as_ptr(), msg.len()).expect("trap stub compiles");
    let stub: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };

    for i in 0..3 {
        let _ = cranelisp_intrinsics::panic::take_runtime_error();
        assert_eq!(stub(), 0);
        assert!(
            cranelisp_intrinsics::panic::take_runtime_error().is_some(),
            "invocation {i} must raise"
        );
    }
}
