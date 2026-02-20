use cranelisp::ast::{Defn, Expr, ReplInput};
use cranelisp::ast_builder::{build_program, parse_program, parse_repl_input};
use cranelisp::codegen::{FnSlot, GotReference};
use cranelisp::display::{format_trait_decl, format_trait_method_type};
use cranelisp::error::CranelispError;
use cranelisp::jit::Jit;
use cranelisp::macro_expand::{compile_macro, expand_sexp, expand_sexps, flatten_begin, is_defmacro, parse_defmacro};
use cranelisp::module::CompiledModule;
use cranelisp::names::ModuleFullPath;
use cranelisp::sexp::parse_sexps;
use cranelisp::typechecker::{SymbolInfo, TypeChecker};
use cranelisp::types::Type;
use std::collections::HashMap;
use std::path::Path;

const PRELUDE: &str = include_str!("test_prelude.cl");

/// Clone the accumulated fn_slots and pre-register the current function so it can reference itself.
fn fn_slots_with(
    base: &HashMap<String, FnSlot>,
    got_addr: i64,
    defn: &Defn,
    slot: usize,
) -> HashMap<String, FnSlot> {
    let mut fn_slots = base.clone();
    fn_slots.insert(
        defn.name.clone(),
        FnSlot {
            got_ref: GotReference::Immediate(got_addr),
            slot,
            param_count: defn.params.len(),
        },
    );
    fn_slots
}

/// Record a compiled function in the accumulated fn_slots map.
fn record_fn_slot(
    fn_slots: &mut HashMap<String, FnSlot>,
    got_addr: i64,
    name: &str,
    slot: usize,
    param_count: usize,
) {
    fn_slots.insert(
        name.to_string(),
        FnSlot {
            got_ref: GotReference::Immediate(got_addr),
            slot,
            param_count,
        },
    );
}

/// Try to load the stdio platform DLL on both JIT and type checker.
/// Returns Ok(()) if loaded, Err if DLL not found (tests can still run without it).
fn try_load_stdio_platform(jit: &mut Jit, tc: &mut TypeChecker) {
    if let Some(dll_path) = cranelisp::platform::resolve_platform_path("stdio") {
        if let Ok((name, _version, descriptors)) = jit.load_platform(&dll_path) {
            let _ = tc.register_platform(&name, &descriptors);
            jit.populate_builtin_func_ids(&mut tc.modules);
            tc.install_synthetic_bare_names();
        }
    }
}

/// Filter out (platform ...) and (import ...) declarations from sexps.
/// These are module-level declarations handled elsewhere; the simple compile path skips them.
fn strip_module_decls(sexps: Vec<cranelisp::sexp::Sexp>) -> Vec<cranelisp::sexp::Sexp> {
    sexps
        .into_iter()
        .filter(|sexp| {
            if let cranelisp::sexp::Sexp::List(children, _) = sexp {
                if let Some(cranelisp::sexp::Sexp::Symbol(head, _)) = children.first() {
                    return head != "platform" && head != "import" && head != "export" && head != "mod";
                }
            }
            true
        })
        .collect()
}

/// Unwrap an IOVal heap pointer to get the inner value.
/// IOVal layout: [tag: i64 (=0), value: i64] — value at ptr+8.
fn unwrap_io_val(ptr: i64) -> i64 {
    unsafe { *((ptr as *const i64).add(1)) }
}

fn compile_and_run(src: &str) -> Result<i64, CranelispError> {
    let prelude = parse_program(PRELUDE)?;

    // Parse user source as sexps for macro expansion
    let user_sexps = parse_sexps(src)?;
    // Strip module-level declarations (platform, import, export, mod)
    let user_sexps = strip_module_decls(user_sexps);

    // Create macro session for prelude + user macro compilation
    let mut macro_session = cranelisp::repl::ReplSession::new()?;
    macro_session.load_prelude();

    // Compile user defmacros
    for sexp in &user_sexps {
        if is_defmacro(sexp) {
            let info = parse_defmacro(sexp)?;
            let ptr = compile_macro(
                &mut macro_session.tc,
                &mut macro_session.jit,
                &info,
                Some(&macro_session.macro_env),
            )?;
            macro_session.macro_env.register(
                info.name,
                ptr,
                info.docstring,
                info.fixed_params,
                info.rest_param,
                Some(info.body_sexp),
            );
        }
    }

    // Expand user code using prelude + user macros
    let expanded = expand_sexps(user_sexps, &macro_session.macro_env)?;
    let user = build_program(&expanded)?;

    let program: Vec<_> = prelude.into_iter().chain(user).collect();
    let mut tc = TypeChecker::new();
    let mut jit = Jit::new()?;
    // Load stdio platform DLL if available (for tests that use print)
    try_load_stdio_platform(&mut jit, &mut tc);
    let result = tc.check_program(&program)?;
    let multi_defns = tc.build_multi_defns(&program);
    jit.populate_builtin_func_ids(&mut tc.modules);
    let raw = jit.compile_and_run(&program, &multi_defns, &result, &tc)?;
    // main() returns IO value — unwrap the IOVal to get inner result
    Ok(unwrap_io_val(raw))
}

#[test]
fn hello() {
    let result = compile_and_run(r#"(defn main [] (print "hello"))"#).unwrap();
    assert_eq!(result, 0); // print returns 0
}

#[test]
fn factorial() {
    let src = r#"
        (defn fact [n]
          (if (= n 0)
            1
            (* n (fact (- n 1)))))
        (defn main [] (pure (fact 10)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 3628800);
}

#[test]
fn fibonacci() {
    let src = r#"
        (defn fib [n]
          (if (<= n 1)
            n
            (+ (fib (- n 1)) (fib (- n 2)))))
        (defn main [] (pure (fib 10)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 55);
}

#[test]
fn nested_let() {
    let src = r#"
        (defn main []
          (pure (let [x 10
                y (+ x 5)
                z (* y 2)]
            z)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 30);
}

#[test]
fn chained_function_calls() {
    let src = r#"
        (defn double [x] (* x 2))
        (defn add-one [x] (+ x 1))
        (defn main [] (pure (double (add-one 5))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 12);
}

#[test]
fn comparison_operators() {
    let src = r#"
        (defn main []
          (pure (let [a (if (= 5 5) 1 0)
                b (if (< 3 5) 1 0)
                c (if (> 5 3) 1 0)
                d (if (<= 3 3) 1 0)
                e (if (>= 5 3) 1 0)]
            (+ a (+ b (+ c (+ d e)))))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 5); // all comparisons true
}

#[test]
fn forward_reference() {
    let src = r#"
        (defn main [] (pure (helper 7)))
        (defn helper [x] (+ x 3))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 10);
}

#[test]
fn type_error_add_bool() {
    let src = "(defn main [] (pure (+ 1 true)))";
    let result = compile_and_run(src);
    assert!(result.is_err());
    match result.unwrap_err() {
        CranelispError::TypeError { .. } => {}
        other => panic!("expected TypeError, got: {:?}", other),
    }
}

#[test]
fn arithmetic() {
    let src = r#"
        (defn main []
          (pure (let [a (+ 10 20)
                b (- a 5)
                c (* b 2)
                d (/ c 5)]
            d)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 10); // (10+20-5)*2/5 = 50/5 = 10
}

#[test]
fn nested_if() {
    let src = r#"
        (defn classify [n]
          (if (< n 0)
            -1
            (if (= n 0) 0 1)))
        (defn main []
          (pure (+ (classify -5) (+ (classify 0) (classify 42)))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0); // -1 + 0 + 1
}

// ── REPL integration tests ──────────────────────────────────────────────

/// Helper: set up a REPL session (TypeChecker + Jit), feed it inputs, return results.
struct ReplSession {
    tc: TypeChecker,
    jit: Jit,
    /// Accumulated fn_slots map — updated after each successful compilation.
    fn_slots: HashMap<String, FnSlot>,
}

impl ReplSession {
    fn new() -> Self {
        let mut tc = TypeChecker::new();
        tc.init_builtins();
        let mut jit = Jit::new().unwrap();
        // Load stdio platform DLL if available
        try_load_stdio_platform(&mut jit, &mut tc);
        tc.install_synthetic_bare_names();
        jit.populate_builtin_func_ids(&mut tc.modules);
        let mut accumulated = HashMap::new();

        // Ensure "user" module exists and has a GOT
        let mod_path = ModuleFullPath::from("user");
        let cm = tc.modules.entry(mod_path.clone())
            .or_insert_with(|| CompiledModule::new(mod_path.clone()));
        cm.ensure_got();
        let got_addr = cm.got_table_addr().unwrap();

        // Load prelude: register types, traits, validate and compile impls
        let prelude_program = parse_program(PRELUDE).unwrap();
        for item in &prelude_program {
            if matches!(item, cranelisp::ast::TopLevel::TypeDef { .. }) {
                tc.register_type_def(item);
            }
        }
        jit.register_type_defs(&tc);
        for item in &prelude_program {
            match item {
                cranelisp::ast::TopLevel::TraitDecl(td) => {
                    for method in &td.methods {
                        jit.register_trait_method(&method.name);
                    }
                    tc.register_trait_public(td);
                }
                cranelisp::ast::TopLevel::TraitImpl(ti) => {
                    tc.validate_impl_public(ti).unwrap();
                    tc.register_impl(ti);
                    let target = ti.impl_target_mangled();
                    for method in &ti.methods {
                        let mangled = cranelisp::ast::Defn {
                            visibility: cranelisp::ast::Visibility::Public,
                            name: format!("{}${}", method.name, target),
                            docstring: None,
                            params: method.params.clone(),
                            param_annotations: method.param_annotations.clone(),
                            body: method.body.clone(),
                            span: method.span,
                        };
                        tc.check_defn(&mangled).unwrap();
                        let mut mr = tc.resolve_methods().unwrap();
                        tc.resolve_overloads(&mut mr).unwrap();
                        let et = tc.resolve_expr_types();
                        let scheme = tc.finalize_defn_type(&mangled.name);
                        let mod_path = ModuleFullPath::from("user");
                        let slot = tc.modules.get_mut(&mod_path).unwrap()
                            .allocate_got_slot(mangled.span).unwrap();
                        let slots = fn_slots_with(&accumulated, got_addr, &mangled, slot);
                        let meta = jit.compile_defn(&mangled, &scheme, &mr, &et, slot, &slots, &tc.modules)
                            .unwrap();
                        tc.modules.get_mut(&mod_path).unwrap()
                            .write_got_slot(slot, meta.code_ptr);
                        record_fn_slot(&mut accumulated, got_addr, &mangled.name, slot, mangled.params.len());
                    }
                }
                cranelisp::ast::TopLevel::Defn(defn) => {
                    tc.check_defn(defn).unwrap();
                    let mut mr = tc.resolve_methods().unwrap();
                    tc.resolve_overloads(&mut mr).unwrap();
                    let et = tc.resolve_expr_types();
                    let scheme = tc.finalize_defn_type(&defn.name);
                    let mod_path = ModuleFullPath::from("user");
                    let slot = tc.modules.get_mut(&mod_path).unwrap()
                        .allocate_got_slot(defn.span).unwrap();
                    let slots = fn_slots_with(&accumulated, got_addr, defn, slot);
                    let meta = jit.compile_defn(defn, &scheme, &mr, &et, slot, &slots, &tc.modules)
                        .unwrap();
                    tc.modules.get_mut(&mod_path).unwrap()
                        .write_got_slot(slot, meta.code_ptr);
                    record_fn_slot(&mut accumulated, got_addr, &defn.name, slot, defn.params.len());
                }
                cranelisp::ast::TopLevel::DefnMulti { name, variants, .. } => {
                    let checked = tc.check_defn_multi(name, variants).unwrap();
                    let mut mr = tc.resolve_methods().unwrap();
                    tc.resolve_overloads(&mut mr).unwrap();
                    let et = tc.resolve_expr_types();
                    for (mangled_name, mangled_defn, _scheme) in &checked {
                        let scheme = tc.finalize_defn_type(mangled_name);
                        let mod_path = ModuleFullPath::from("user");
                        let slot = tc.modules.get_mut(&mod_path).unwrap()
                            .allocate_got_slot(mangled_defn.span).unwrap();
                        let slots = fn_slots_with(&accumulated, got_addr, mangled_defn, slot);
                        let meta = jit.compile_defn(mangled_defn, &scheme, &mr, &et, slot, &slots, &tc.modules)
                            .unwrap();
                        tc.modules.get_mut(&mod_path).unwrap()
                            .write_got_slot(slot, meta.code_ptr);
                        record_fn_slot(&mut accumulated, got_addr, &mangled_defn.name, slot, mangled_defn.params.len());
                    }
                }
                _ => {}
            }
        }

        ReplSession { tc, jit, fn_slots: accumulated }
    }

    /// Feed a defn, return Ok(()) on success.
    fn defn(&mut self, src: &str) -> Result<(), CranelispError> {
        let input = parse_repl_input(src)?;
        match input {
            ReplInput::Defn(defn) => {
                self.tc.check_defn(&defn)?;
                let mut method_resolutions = self.tc.resolve_methods()?;
                self.tc.resolve_overloads(&mut method_resolutions)?;
                let et = self.tc.resolve_expr_types();
                let scheme = self.tc.finalize_defn_type(&defn.name);
                if scheme.is_constrained() {
                    self.tc.register_constrained_fn(&defn, &scheme);
                } else {
                    let mod_path = ModuleFullPath::from("user");
                    let cm = self.tc.modules.get_mut(&mod_path).unwrap();
                    let got_addr = cm.got_table_addr().unwrap();
                    let slot = self.fn_slots.get(&defn.name).map(|s| s.slot)
                        .unwrap_or_else(|| {
                            self.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                                .allocate_got_slot(defn.span).unwrap()
                        });
                    let slots = fn_slots_with(&self.fn_slots, got_addr, &defn, slot);
                    let meta = self.jit
                        .compile_defn(&defn, &scheme, &method_resolutions, &et, slot, &slots, &self.tc.modules)?;
                    self.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                        .write_got_slot(slot, meta.code_ptr);
                    record_fn_slot(&mut self.fn_slots, got_addr, &defn.name, slot, defn.params.len());
                }
                Ok(())
            }
            _ => panic!("expected defn, got expr"),
        }
    }

    /// Feed a multi-sig defn, return Ok(()) on success.
    fn defn_multi(&mut self, src: &str) -> Result<(), CranelispError> {
        let input = parse_repl_input(src)?;
        match input {
            ReplInput::DefnMulti { name, variants, .. } => {
                let checked = self.tc.check_defn_multi(&name, &variants)?;
                let mut method_resolutions = self.tc.resolve_methods()?;
                self.tc.resolve_overloads(&mut method_resolutions)?;
                let et = self.tc.resolve_expr_types();
                let mod_path = ModuleFullPath::from("user");
                let got_addr = self.tc.modules.get(&mod_path).unwrap().got_table_addr().unwrap();
                for (mangled_name, mangled_defn, _scheme) in &checked {
                    let scheme = self.tc.finalize_defn_type(mangled_name);
                    let slot = self.fn_slots.get(&mangled_defn.name).map(|s| s.slot)
                        .unwrap_or_else(|| {
                            self.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                                .allocate_got_slot(mangled_defn.span).unwrap()
                        });
                    let slots = fn_slots_with(&self.fn_slots, got_addr, mangled_defn, slot);
                    let meta = self.jit.compile_defn(
                        mangled_defn,
                        &scheme,
                        &method_resolutions,
                        &et,
                        slot,
                        &slots,
                        &self.tc.modules,
                    )?;
                    self.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                        .write_got_slot(slot, meta.code_ptr);
                    record_fn_slot(&mut self.fn_slots, got_addr, &mangled_defn.name, slot, mangled_defn.params.len());
                }
                Ok(())
            }
            _ => panic!("expected defn_multi"),
        }
    }

    /// Feed an expression, return its i64 result.
    /// If the expression type is IO, unwraps the IOVal to return the inner value.
    fn eval(&mut self, src: &str) -> Result<i64, CranelispError> {
        let input = parse_repl_input(src)?;
        match input {
            ReplInput::Expr(expr) => {
                let expr_type = self.tc.check_expr(&expr)?;
                let resolved_type = self.tc.resolve(&expr_type);
                let mut method_resolutions = self.tc.resolve_methods()?;
                self.tc.resolve_overloads(&mut method_resolutions)?;
                let et = self.tc.resolve_expr_types();

                // On-demand monomorphisation
                let (mono_defns, mono_dispatches) = self.tc.monomorphise_all()?;
                method_resolutions.extend(mono_dispatches);
                let mod_path = ModuleFullPath::from("user");
                let got_addr = self.tc.modules.get(&mod_path).unwrap().got_table_addr().unwrap();
                for (mono, _defining_mod) in &mono_defns {
                    let mono_scheme = cranelisp::types::Scheme::mono(cranelisp::types::Type::Fn(
                        mono.defn
                            .params
                            .iter()
                            .map(|_| cranelisp::types::Type::Int)
                            .collect(),
                        Box::new(cranelisp::types::Type::Int),
                    ));
                    let slot = self.fn_slots.get(&mono.defn.name).map(|s| s.slot)
                        .unwrap_or_else(|| {
                            self.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                                .allocate_got_slot(mono.defn.span).unwrap()
                        });
                    let slots = fn_slots_with(&self.fn_slots, got_addr, &mono.defn, slot);
                    let meta = self.jit.compile_defn_with_resolutions(
                        &mono.defn,
                        &mono_scheme,
                        &method_resolutions,
                        Some(&mono.resolutions),
                        &et,
                        slot,
                        &slots,
                        &self.tc.modules,
                    )?;
                    self.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                        .write_got_slot(slot, meta.code_ptr);
                    record_fn_slot(&mut self.fn_slots, got_addr, &mono.defn.name, slot, mono.defn.params.len());
                }

                let raw = self.jit.eval_expr(&expr, &method_resolutions, &et, &self.fn_slots, &self.tc.modules)?;
                // If expression type is IO, unwrap the IOVal heap pointer
                if matches!(&resolved_type, Type::ADT(name, _) if name == "IO") {
                    Ok(unwrap_io_val(raw))
                } else {
                    Ok(raw)
                }
            }
            _ => panic!("expected expr, got defn"),
        }
    }

    /// Look up the resolved type for a name in the type environment.
    fn lookup_type(&self, name: &str) -> Option<Type> {
        self.tc
            .lookup_env(name)
            .map(|scheme| self.tc.resolve(&scheme.ty))
    }

    /// Feed a trait declaration.
    fn trait_decl(&mut self, src: &str) -> Result<(), CranelispError> {
        let input = parse_repl_input(src)?;
        match input {
            ReplInput::TraitDecl(td) => {
                for method in &td.methods {
                    self.jit.register_trait_method(&method.name);
                }
                self.tc.register_trait_public(&td);
                Ok(())
            }
            _ => panic!("expected trait decl"),
        }
    }

    /// Check if a bare expression is a trait method var and return its formatted type.
    fn trait_method_type(&mut self, src: &str) -> Option<String> {
        let input = parse_repl_input(src).ok()?;
        match input {
            ReplInput::Expr(ref expr) => {
                self.tc.check_expr(expr).ok()?;
                let mut mr = self.tc.resolve_methods().ok()?;
                let _ = self.tc.resolve_overloads(&mut mr).ok()?;
                if let Expr::Var { name, .. } = expr {
                    if let Some(trait_name) = self.tc.get_method_trait(name) {
                        if let Some(decl) = self.tc.get_trait(trait_name) {
                            if let Some(sig) = decl.methods.iter().find(|m| m.name == *name) {
                                return Some(format_trait_method_type(sig, trait_name));
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Check if a bare expression is a trait name and return its formatted declaration.
    fn trait_display(&mut self, src: &str) -> Option<String> {
        let input = parse_repl_input(src).ok()?;
        match input {
            ReplInput::Expr(ref expr) => {
                if let Expr::Var { name, .. } = expr {
                    if let Some(decl) = self.tc.get_trait(name) {
                        return Some(format!("{} :: {}", name, format_trait_decl(decl)));
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Feed a deftype declaration — registers type, constructors, and accessors.
    fn typedef(&mut self, src: &str) -> Result<(), CranelispError> {
        let input = parse_repl_input(src)?;
        match input {
            ReplInput::TypeDef {
                name,
                type_params,
                constructors,
                span,
                ..
            } => {
                let td = cranelisp::ast::TopLevel::TypeDef {
                    visibility: cranelisp::ast::Visibility::Public,
                    docstring: None,
                    name,
                    type_params,
                    constructors,
                    span,
                };
                self.tc.register_type_def(&td);
                self.jit.register_type_defs(&self.tc);
                Ok(())
            }
            _ => panic!("expected typedef"),
        }
    }

    /// Feed a trait impl — validates, type-checks, and compiles the methods.
    fn trait_impl(&mut self, src: &str) -> Result<(), CranelispError> {
        let input = parse_repl_input(src)?;
        match input {
            ReplInput::TraitImpl(ti) => {
                self.tc.validate_impl_public(&ti)?;
                self.tc.register_impl(&ti);
                let self_type = self.tc.resolve_impl_self_type(&ti)?;
                let target = ti.impl_target_mangled();
                let mod_path = ModuleFullPath::from("user");
                let got_addr = self.tc.modules.get(&mod_path).unwrap().got_table_addr().unwrap();
                for method in &ti.methods {
                    let mangled = cranelisp::ast::Defn {
                        visibility: cranelisp::ast::Visibility::Public,
                        name: format!("{}${}", method.name, target),
                        docstring: None,
                        params: method.params.clone(),
                        param_annotations: method.param_annotations.clone(),
                        body: method.body.clone(),
                        span: method.span,
                    };
                    self.tc.check_impl_method(&mangled, &self_type)?;
                    let mut method_resolutions = self.tc.resolve_methods()?;
                    self.tc.resolve_overloads(&mut method_resolutions)?;
                    let et = self.tc.resolve_expr_types();
                    let scheme = self.tc.finalize_defn_type(&mangled.name);
                    if scheme.is_constrained() {
                        self.tc.register_constrained_fn(&mangled, &scheme);
                    } else {
                        let slot = self.fn_slots.get(&mangled.name).map(|s| s.slot)
                            .unwrap_or_else(|| {
                                self.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                                    .allocate_got_slot(mangled.span).unwrap()
                            });
                        let slots = fn_slots_with(&self.fn_slots, got_addr, &mangled, slot);
                        let meta = self.jit.compile_defn(
                            &mangled,
                            &scheme,
                            &method_resolutions,
                            &et,
                            slot,
                            &slots,
                            &self.tc.modules,
                        )?;
                        self.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                            .write_got_slot(slot, meta.code_ptr);
                        record_fn_slot(&mut self.fn_slots, got_addr, &mangled.name, slot, mangled.params.len());
                    }
                }
                Ok(())
            }
            _ => panic!("expected trait impl"),
        }
    }
}

#[test]
fn repl_eval_expression() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(+ 1 2)").unwrap(), 3);
    assert_eq!(r.eval("(* 6 7)").unwrap(), 42);
    assert_eq!(r.eval("(if (< 1 2) 10 20)").unwrap(), 10);
}

#[test]
fn repl_define_and_call() {
    let mut r = ReplSession::new();
    r.defn("(defn add1 [x] (+ x 1))").unwrap();
    assert_eq!(r.eval("(add1 5)").unwrap(), 6);
}

#[test]
fn repl_chained_calls() {
    let mut r = ReplSession::new();
    r.defn("(defn add1 [x] (+ x 1))").unwrap();
    r.defn("(defn double [x] (* x 2))").unwrap();
    r.defn("(defn pipeline [x] (double (add1 x)))").unwrap();
    assert_eq!(r.eval("(pipeline 5)").unwrap(), 12);
}

#[test]
fn repl_redefinition_updates_callers() {
    let mut r = ReplSession::new();
    r.defn("(defn add1 [x] (+ x 1))").unwrap();
    r.defn("(defn double [x] (* x 2))").unwrap();
    r.defn("(defn pipeline [x] (double (add1 x)))").unwrap();
    assert_eq!(r.eval("(pipeline 5)").unwrap(), 12);

    // Redefine add1 to add 10 instead of 1
    r.defn("(defn add1 [x] (+ x 10))").unwrap();
    // pipeline should now use the new add1
    assert_eq!(r.eval("(pipeline 5)").unwrap(), 30);
}

#[test]
fn repl_recursive_function() {
    let mut r = ReplSession::new();
    r.defn("(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))")
        .unwrap();
    assert_eq!(r.eval("(fact 10)").unwrap(), 3628800);
}

#[test]
fn repl_type_error_recovers() {
    let mut r = ReplSession::new();
    // This should fail with a type error
    let result = r.eval("(+ 1 true)");
    assert!(result.is_err());
    // But the session should still work after the error
    assert_eq!(r.eval("(+ 1 2)").unwrap(), 3);
}

#[test]
fn repl_print_builtin() {
    let mut r = ReplSession::new();
    // print returns 0
    assert_eq!(r.eval(r#"(print "hello")"#).unwrap(), 0);
}

#[test]
fn repl_multiple_params() {
    let mut r = ReplSession::new();
    r.defn("(defn add [x y] (+ x y))").unwrap();
    assert_eq!(r.eval("(add 3 4)").unwrap(), 7);
}

// ── Lambda / first-class function tests ─────────────────────────────────

#[test]
fn lambda_immediate_call() {
    let src = r#"
        (defn main [] (pure ((fn [x] (+ x 1)) 5)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 6);
}

#[test]
fn lambda_in_let() {
    let src = r#"
        (defn main [] (pure (let [f (fn [x] (* x 2))] (f 5))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 10);
}

#[test]
fn lambda_passed_to_function() {
    let src = r#"
        (defn apply-fn [f x] (f x))
        (defn main [] (pure (apply-fn (fn [x] (* x 2)) 5)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 10);
}

#[test]
fn named_function_as_value() {
    let src = r#"
        (defn double [x] (* x 2))
        (defn apply-fn [f x] (f x))
        (defn main [] (pure (apply-fn double 5)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 10);
}

#[test]
fn operator_as_value() {
    // (let [f +] (f 3 4)) → 7
    let src = r#"
        (defn main [] (pure (let [f +] (f 3 4))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 7);
}

#[test]
fn operator_auto_curry() {
    // (let [inc (+ 1)] (inc 5)) → 6
    let src = r#"
        (defn main [] (pure (let [inc (+ 1)] (inc 5))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 6);
}

#[test]
fn operator_higher_order() {
    // Pass + to a higher-order function
    let src = r#"
        (defn apply2 [f x y] (f x y))
        (defn main [] (pure (apply2 + 3 4)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 7);
}

#[test]
fn lambda_zero_params() {
    let src = r#"
        (defn main [] (pure (let [f (fn [] 42)] (f))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn lambda_multi_params() {
    let src = r#"
        (defn main [] (pure ((fn [x y] (+ x y)) 3 4)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 7);
}

#[test]
fn repl_lambda_immediate() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("((fn [x] (+ x 1)) 5)").unwrap(), 6);
}

#[test]
fn repl_lambda_in_let() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(let [f (fn [x] (* x 2))] (f 5))").unwrap(), 10);
}

#[test]
fn repl_higher_order_function() {
    let mut r = ReplSession::new();
    r.defn("(defn apply-fn [f x] (f x))").unwrap();
    assert_eq!(r.eval("(apply-fn (fn [x] (+ x 10)) 5)").unwrap(), 15);
}

#[test]
fn repl_named_function_as_value() {
    let mut r = ReplSession::new();
    r.defn("(defn double [x] (* x 2))").unwrap();
    r.defn("(defn apply-fn [f x] (f x))").unwrap();
    assert_eq!(r.eval("(apply-fn double 5)").unwrap(), 10);
}

// ── Closure / capture tests ─────────────────────────────────────────────

#[test]
fn closure_simple_capture() {
    let src = r#"
        (defn make-adder [n] (fn [x] (+ n x)))
        (defn main [] (pure (let [add5 (make-adder 5)] (add5 3))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 8);
}

#[test]
fn closure_multiple_captures() {
    let src = r#"
        (defn main []
          (pure (let [a 1 b 2]
            ((fn [x] (+ x (+ a b))) 10))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 13);
}

#[test]
fn closure_returned_from_function() {
    let src = r#"
        (defn make-multiplier [n] (fn [x] (* n x)))
        (defn main [] (pure (let [triple (make-multiplier 3)] (triple 7))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 21);
}

#[test]
fn closure_nested() {
    // Closure returning a closure
    let src = r#"
        (defn make-adder [n]
          (fn [x] (+ n x)))
        (defn apply-fn [f x] (f x))
        (defn main []
          (pure (let [add10 (make-adder 10)]
            (apply-fn add10 5))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 15);
}

#[test]
fn repl_closure_simple() {
    let mut r = ReplSession::new();
    r.defn("(defn make-adder [n] (fn [x] (+ n x)))").unwrap();
    assert_eq!(r.eval("(let [add5 (make-adder 5)] (add5 3))").unwrap(), 8);
}

#[test]
fn repl_closure_multiple_captures() {
    let mut r = ReplSession::new();
    assert_eq!(
        r.eval("(let [a 10 b 20] ((fn [x] (+ x (+ a b))) 5))")
            .unwrap(),
        35
    );
}

#[test]
fn closure_with_higher_order() {
    // Pass a closure to a higher-order function
    let src = r#"
        (defn apply-fn [f x] (f x))
        (defn make-adder [n] (fn [x] (+ n x)))
        (defn main [] (pure (apply-fn (make-adder 100) 42)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 142);
}

// ── IO / do / pure / bind tests ─────────────────────────────────────────

#[test]
fn do_sequences_effects() {
    let src = r#"
        (defn main []
          (do
            (print "1")
            (print "2")
            (print "3")))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0); // last print returns 0
}

#[test]
fn pure_lifts_value() {
    let src = r#"
        (defn main [] (pure 42))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn bind_extracts_and_continues() {
    let src = r#"
        (defn main []
          (bind (print "hello")
            (fn [result] (pure (+ result 1)))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 1); // print returns 0, 0 + 1 = 1
}

#[test]
fn do_with_pure_in_if() {
    let src = r#"
        (defn main []
          (if true
            (print "hello")
            (pure 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0); // print "hello" returns 0
}

#[test]
fn bind_chain() {
    let src = r#"
        (defn main []
          (bind (print "a")
            (fn [_]
              (bind (print "b")
                (fn [_] (print "c"))))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn full_io_program() {
    let src = r#"
        (defn greet [x] (print x))
        (defn main []
          (do
            (greet "hello")
            (greet "world")
            (pure 99)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 99);
}

#[test]
fn repl_do_expression() {
    // do is now a macro — test ReplSession doesn't expand macros, use expanded form
    let mut r = ReplSession::new();
    assert_eq!(r.eval(r#"(let [_ (print "a")] (print "b"))"#).unwrap(), 0);
}

#[test]
fn repl_pure_expression() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(pure 42)").unwrap(), 42);
}

#[test]
fn repl_bind_expression() {
    let mut r = ReplSession::new();
    assert_eq!(
        r.eval(r#"(bind (print "x") (fn [x] (pure (+ x 1))))"#)
            .unwrap(),
        1
    );
}

#[test]
fn builtin_as_value() {
    let src = r#"
        (defn apply-fn [f x] (f x))
        (defn main [] (apply-fn print "hello"))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0); // print returns 0
}

#[test]
fn repl_builtin_as_value() {
    let mut r = ReplSession::new();
    r.defn("(defn apply-fn [f x] (f x))").unwrap();
    assert_eq!(r.eval(r#"(apply-fn print "hello")"#).unwrap(), 0);
}

// ── String tests ────────────────────────────────────────────────────────

#[test]
fn string_literal_print() {
    let src = r#"(defn main [] (print "hello, world!"))"#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn string_type_error_int_to_print() {
    // print now takes String, not Int
    let src = "(defn main [] (print 42))";
    assert!(compile_and_run(src).is_err());
}

#[test]
fn string_in_let() {
    let src = r#"
        (defn main [] (let [s "hello"] (print s)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn repl_string_literal() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval(r#"(print "hello")"#).unwrap(), 0);
}

// ── Trait tests ────────────────────────────────────────────────────────

#[test]
fn builtin_show_int() {
    let src = r#"
        (defn main [] (print (show 42)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn builtin_show_bool() {
    let src = r#"
        (defn main [] (print (show true)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn builtin_show_string() {
    let src = r#"
        (defn main [] (print (show "hello")))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn user_defined_trait_impl() {
    let src = r#"
        (deftrait Doubled
          (doubled [self] Int))

        (impl Doubled Int
          (defn doubled [x] (* x 2)))

        (defn main [] (pure (doubled 21)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn user_defined_trait_with_show() {
    let src = r#"
        (deftrait Doubled
          (doubled [self] Int))

        (impl Doubled Int
          (defn doubled [x] (* x 2)))

        (defn main [] (print (show (doubled 21))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn repl_builtin_show_int() {
    let mut r = ReplSession::new();
    // show 42 returns a string pointer; print it
    assert_eq!(r.eval(r#"(print (show 42))"#).unwrap(), 0);
}

#[test]
fn repl_builtin_show_bool() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval(r#"(print (show true))"#).unwrap(), 0);
}

#[test]
fn repl_user_defined_trait() {
    let mut r = ReplSession::new();
    r.trait_decl("(deftrait Doubled (doubled [self] Int))")
        .unwrap();
    r.trait_impl("(impl Doubled Int (defn doubled [x] (* x 2)))")
        .unwrap();
    assert_eq!(r.eval("(doubled 21)").unwrap(), 42);
}

#[test]
fn repl_user_trait_with_show() {
    let mut r = ReplSession::new();
    r.trait_decl("(deftrait Doubled (doubled [self] Int))")
        .unwrap();
    r.trait_impl("(impl Doubled Int (defn doubled [x] (* x 2)))")
        .unwrap();
    assert_eq!(r.eval(r#"(print (show (doubled 21)))"#).unwrap(), 0);
}

// ── Bare trait method type display tests ────────────────────────────────

#[test]
fn repl_bare_builtin_trait_method_type() {
    let mut r = ReplSession::new();
    assert_eq!(
        r.trait_method_type("show"),
        Some("(Fn [:Display a] String)".into())
    );
}

#[test]
fn repl_bare_user_trait_method_type() {
    let mut r = ReplSession::new();
    r.trait_decl("(deftrait Doubled (doubled [self] Int))")
        .unwrap();
    assert_eq!(
        r.trait_method_type("doubled"),
        Some("(Fn [:Doubled a] Int)".into())
    );
}

#[test]
fn repl_non_trait_var_returns_none() {
    let mut r = ReplSession::new();
    r.defn("(defn inc [x] (+ x 1))").unwrap();
    assert_eq!(r.trait_method_type("inc"), None);
}

// ── Bare trait name display tests ───────────────────────────────────

#[test]
fn repl_bare_builtin_trait_display() {
    let mut r = ReplSession::new();
    assert_eq!(
        r.trait_display("Display"),
        Some("Display :: (deftrait Display (show [self] String))".into())
    );
}

#[test]
fn repl_bare_user_trait_display() {
    let mut r = ReplSession::new();
    r.trait_decl("(deftrait Doubled (doubled [self] Int))")
        .unwrap();
    assert_eq!(
        r.trait_display("Doubled"),
        Some("Doubled :: (deftrait Doubled (doubled [self] Int))".into())
    );
}

#[test]
fn repl_bare_trait_name_not_function() {
    let mut r = ReplSession::new();
    r.defn("(defn inc [x] (+ x 1))").unwrap();
    assert_eq!(r.trait_display("inc"), None);
}

#[test]
fn repl_trait_error_recovers() {
    let mut r = ReplSession::new();
    r.trait_decl("(deftrait Double (double [self] self))")
        .unwrap();
    r.trait_impl("(impl Double Int (defn double [x] (+ x x)))")
        .unwrap();
    assert_eq!(r.eval("(double 3)").unwrap(), 6);
    // This should fail — no impl for Bool
    assert!(r.eval("(double true)").is_err());
    // After the error, valid calls should still work
    assert_eq!(r.eval("(double 6)").unwrap(), 12);
}

// ── Multi-signature / overload dispatch tests ──────────────────────────

#[test]
fn multi_sig_different_arities() {
    let src = r#"
        (defn add
          ([x y] (add-i64 x y))
          ([x y z] (add-i64 x (add-i64 y z))))
        (defn main [] (pure (add-i64 (add 1 2) (add 1 2 3))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 9); // 3 + 6
}

#[test]
fn multi_sig_type_based_dispatch() {
    let src = r#"
        (defn choose
          ([x y] (add-i64 x y))
          ([x y] (if y x 0)))
        (defn main [] (pure (add-i64 (choose 10 20) (choose 5 true))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 35); // 30 + 5
}

#[test]
fn multi_sig_duplicate_signature_error() {
    let src = r#"
        (defn dup
          ([x] (+ x 1))
          ([y] (+ y 2)))
        (defn main [] (pure (dup 1)))
    "#;
    let result = compile_and_run(src);
    assert!(result.is_err());
}

// ── Auto-curry tests ───────────────────────────────────────────────────

#[test]
fn auto_curry_simple() {
    let src = r#"
        (defn add [x y] (add-i64 x y))
        (defn main [] (pure (let [f (add 10)] (f 5))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 15);
}

#[test]
fn auto_curry_higher_order() {
    let src = r#"
        (defn add [x y] (add-i64 x y))
        (defn apply-fn [f x] (f x))
        (defn main [] (pure (apply-fn (add 10) 5)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 15);
}

#[test]
fn auto_curry_multi_sig() {
    let src = r#"
        (defn add
          ([x y] (add-i64 x y))
          ([x y z] (add-i64 x (add-i64 y z))))
        (defn apply-fn [f x] (f x))
        (defn main []
          (do
            (print (show (add 1 2)))
            (print (show (add 1 2 3)))
            (print (show (apply-fn (add 10) 5)))
            (pure 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

// ── REPL multi-sig tests ───────────────────────────────────────────────

#[test]
fn repl_multi_sig_different_arities() {
    let mut r = ReplSession::new();
    r.defn_multi("(defn add ([x y] (add-i64 x y)) ([x y z] (add-i64 x (add-i64 y z))))")
        .unwrap();
    assert_eq!(r.eval("(add 1 2)").unwrap(), 3);
    assert_eq!(r.eval("(add 1 2 3)").unwrap(), 6);
}

#[test]
fn repl_auto_curry() {
    let mut r = ReplSession::new();
    r.defn("(defn add [x y] (add-i64 x y))").unwrap();
    assert_eq!(r.eval("(let [f (add 10)] (f 5))").unwrap(), 15);
}

#[test]
fn repl_multi_sig_auto_curry() {
    let mut r = ReplSession::new();
    r.defn_multi("(defn add ([x y] (add-i64 x y)) ([x y z] (add-i64 x (add-i64 y z))))")
        .unwrap();
    r.defn("(defn apply-fn [f x] (f x))").unwrap();
    assert_eq!(r.eval("(apply-fn (add 10) 5)").unwrap(), 15);
}

// ── Defn type finalization tests (regression) ───────────────────────────

#[test]
fn repl_defn_using_trait_stores_concrete_type() {
    // (defn foo [x y] (add-i64 x y)) should store (fn [Int Int] Int)
    let mut r = ReplSession::new();
    r.defn("(defn foo [x y] (add-i64 x y))").unwrap();
    let ty = r.lookup_type("foo").unwrap();
    assert_eq!(
        ty,
        Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
    );
}

#[test]
fn repl_defn_using_trait_rejects_wrong_type() {
    // After defining foo using add-i64, calling with bools should be a type error
    let mut r = ReplSession::new();
    r.defn("(defn foo [x y] (add-i64 x y))").unwrap();
    assert!(r.eval("(foo true false)").is_err());
}

#[test]
fn repl_defn_using_trait_accepts_correct_type() {
    let mut r = ReplSession::new();
    r.defn("(defn foo [x y] (add-i64 x y))").unwrap();
    assert_eq!(r.eval("(foo 34 35)").unwrap(), 69);
}

#[test]
fn repl_defn_truly_polymorphic_stays_polymorphic() {
    // (defn id [x] x) should remain polymorphic — no trait constraint
    let mut r = ReplSession::new();
    r.defn("(defn id [x] x)").unwrap();
    let ty = r.lookup_type("id").unwrap();
    // Should be (fn [a] a) — has type vars, not concrete
    match &ty {
        Type::Fn(params, _ret) => {
            assert!(matches!(params[0], Type::Var(_)));
        }
        _ => panic!("expected function type, got {:?}", ty),
    }
    // Should work with both Int and Bool
    assert_eq!(r.eval("(id 42)").unwrap(), 42);
    assert_eq!(r.eval("(id true)").unwrap(), 1); // true = 1
}

// ── Float type tests ────────────────────────────────────────────────────

#[test]
fn float_arithmetic() {
    let src = r#"
        (defn main [] (pure (+ 1.5 2.5)))
    "#;
    let result = compile_and_run(src).unwrap();
    let f = f64::from_bits(result as u64);
    assert!((f - 4.0).abs() < 1e-10);
}

#[test]
fn float_comparison() {
    let src = r#"
        (defn main [] (pure (if (< 1.5 2.5) 1 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn float_show() {
    let src = r#"
        (defn main [] (print (show 3.14)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn float_type_error_mixed() {
    // (+ 1 1.0) should be a type error — Int and Float don't mix
    let src = "(defn main [] (pure (+ 1 1.0)))";
    assert!(compile_and_run(src).is_err());
}

#[test]
fn repl_float_eval() {
    let mut r = ReplSession::new();
    let result = r.eval("3.14").unwrap();
    let f = f64::from_bits(result as u64);
    assert!((f - 3.14).abs() < 1e-10);
}

#[test]
fn repl_float_arithmetic() {
    let mut r = ReplSession::new();
    let result = r.eval("(+ 1.0 2.0)").unwrap();
    let f = f64::from_bits(result as u64);
    assert!((f - 3.0).abs() < 1e-10);
}

// --- Constrained polymorphism (monomorphisation) tests ---

#[test]
fn constrained_add_int() {
    let result = compile_and_run(
        r#"
        (defn add [x y] (+ x y))
        (defn main [] (pure (add 1 2)))
    "#,
    )
    .unwrap();
    assert_eq!(result, 3);
}

#[test]
fn constrained_add_float() {
    let result = compile_and_run(
        r#"
        (defn add [x y] (+ x y))
        (defn main [] (pure (add 1.5 2.5)))
    "#,
    )
    .unwrap();
    let f = f64::from_bits(result as u64);
    assert!((f - 4.0).abs() < 1e-10);
}

#[test]
fn constrained_add_both_types() {
    // Same constrained function called with Int and Float in one program
    let result = compile_and_run(
        r#"
        (defn add [x y] (+ x y))
        (defn main [] (do (print (show (add 1.5 2.5))) (pure (add 1 2))))
    "#,
    )
    .unwrap();
    assert_eq!(result, 3);
}

#[test]
fn constrained_never_called_ok() {
    // A constrained function that's never called should not cause an error
    let result = compile_and_run(
        r#"
        (defn add [x y] (+ x y))
        (defn main [] (pure 42))
    "#,
    )
    .unwrap();
    assert_eq!(result, 42);
}

#[test]
fn repl_constrained_fn_int() {
    let mut r = ReplSession::new();
    r.defn("(defn add [x y] (+ x y))").unwrap();
    let result = r.eval("(add 1 2)").unwrap();
    assert_eq!(result, 3);
}

#[test]
fn repl_constrained_fn_float() {
    let mut r = ReplSession::new();
    r.defn("(defn add [x y] (+ x y))").unwrap();
    let result = r.eval("(add 1.5 2.5)").unwrap();
    let f = f64::from_bits(result as u64);
    assert!((f - 4.0).abs() < 1e-10);
}

#[test]
fn repl_constrained_fn_both_types() {
    let mut r = ReplSession::new();
    r.defn("(defn add [x y] (+ x y))").unwrap();
    let int_result = r.eval("(add 1 2)").unwrap();
    assert_eq!(int_result, 3);
    let float_result = r.eval("(add 1.5 2.5)").unwrap();
    let f = f64::from_bits(float_result as u64);
    assert!((f - 4.0).abs() < 1e-10);
}

#[test]
fn repl_constrained_fn_bare_name_describes() {
    let mut r = ReplSession::new();
    r.defn("(defn add [x y] (+ x y))").unwrap();
    // Bare name should be recognised as a constrained function, not error
    match r.tc.describe_symbol("add") {
        Some(SymbolInfo::ConstrainedFn { scheme }) => {
            assert!(scheme.is_constrained());
        }
        other => panic!("expected ConstrainedFn, got {:?}", other.is_some()),
    }
}

#[test]
fn repl_constrained_fn_as_value_errors() {
    let mut r = ReplSession::new();
    r.defn("(defn add [x y] (+ x y))").unwrap();
    // Using constrained fn as a value (e.g. in let binding) should still error
    let result = r.eval("(let [f add] (f 1 2))");
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(err_msg.contains("cannot use constrained function"));
}

#[test]
fn repl_overloaded_fn_bare_name_describes() {
    let mut r = ReplSession::new();
    r.defn_multi("(defn bar ([x] x) ([x y] (+ x y)))").unwrap();
    match r.tc.describe_symbol("bar") {
        Some(SymbolInfo::OverloadedFn { schemes }) => {
            assert_eq!(schemes.len(), 2);
        }
        other => panic!("expected OverloadedFn, got {:?}", other.is_some()),
    }
}

// ── ADT: batch mode tests ──────────────────────────────────────────

#[test]
fn adt_enum_match() {
    let src = r#"
        (deftype Color Red Green Blue)
        (defn color-value [c]
          (match c
            [Red 1
             Green 2
             Blue 3]))
        (defn main [] (pure (color-value Green)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 2);
}

#[test]
fn adt_product_construct_and_match() {
    let src = r#"
        (deftype Point [:Int x :Int y])
        (defn get-x [p]
          (match p
            [(Point px py) px]))
        (defn main [] (pure (get-x (Point 3 4))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 3);
}

#[test]
fn adt_product_get_y() {
    let src = r#"
        (deftype Point [:Int x :Int y])
        (defn get-y [p]
          (match p
            [(Point px py) py]))
        (defn main [] (pure (get-y (Point 3 4))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 4);
}

#[test]
fn adt_sum_type_some_none() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn unwrap-or [opt default]
          (match opt
            [None default
             (Some x) x]))
        (defn main [] (pure (unwrap-or (Some 42) 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn adt_sum_type_none_case() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn unwrap-or [opt default]
          (match opt
            [None default
             (Some x) x]))
        (defn main [] (pure (unwrap-or None 99)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 99);
}

#[test]
fn adt_match_wildcard() {
    let src = r#"
        (deftype Color Red Green Blue)
        (defn is-red [c]
          (match c
            [Red 1
             _ 0]))
        (defn main [] (pure (+ (is-red Red) (is-red Blue))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn adt_match_var_pattern() {
    let src = r#"
        (deftype Color Red Green Blue)
        (defn id-color [c]
          (match c
            [x x]))
        (defn main [] (pure (match (id-color Red) [Red 1 _ 0])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn adt_nested_match() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn add-options [a b]
          (match a
            [None 0
             (Some x)
              (match b
                [None x
                 (Some y) (+ x y)])]))
        (defn main [] (pure (add-options (Some 10) (Some 32))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn adt_shortcut_syntax() {
    let src = r#"
        (deftype Pair [first second])
        (defn get-first [p]
          (match p
            [(Pair a b) a]))
        (defn main [] (pure (get-first (Pair 7 8))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 7);
}

// ── ADT: REPL mode tests ──────────────────────────────────────────

#[test]
fn repl_adt_enum() {
    let mut r = ReplSession::new();
    r.typedef("(deftype Color Red Green Blue)").unwrap();
    assert_eq!(r.eval("Red").unwrap(), 0);
    assert_eq!(r.eval("Green").unwrap(), 1);
    assert_eq!(r.eval("Blue").unwrap(), 2);
}

#[test]
fn repl_adt_enum_match() {
    let mut r = ReplSession::new();
    r.typedef("(deftype Color Red Green Blue)").unwrap();
    assert_eq!(
        r.eval("(match Green [Red 10 Green 20 Blue 30])").unwrap(),
        20
    );
}

#[test]
fn repl_adt_product() {
    let mut r = ReplSession::new();
    r.typedef("(deftype Point [:Int x :Int y])").unwrap();
    let result = r
        .eval("(match (Point 3 4) [(Point px py) (+ px py)])")
        .unwrap();
    assert_eq!(result, 7);
}

#[test]
fn repl_adt_sum_type() {
    let mut r = ReplSession::new();
    r.typedef("(deftype (Option a) None (Some [:a val]))")
        .unwrap();
    assert_eq!(r.eval("(match (Some 42) [None 0 (Some x) x])").unwrap(), 42);
    assert_eq!(r.eval("(match None [None 99 (Some x) x])").unwrap(), 99);
}

#[test]
fn repl_adt_constructor_describes() {
    let mut r = ReplSession::new();
    r.typedef("(deftype (Option a) None (Some [:a val]))")
        .unwrap();
    match r.tc.describe_symbol("Some") {
        Some(SymbolInfo::Constructor { .. }) => {}
        other => panic!("expected Constructor, got {:?}", other.is_some()),
    }
    match r.tc.describe_symbol("Option") {
        Some(SymbolInfo::UserType { type_def }) => {
            assert_eq!(type_def.constructors.len(), 2);
        }
        other => panic!("expected UserType, got {:?}", other.is_some()),
    }
}

// ── ADT: field accessor tests ─────────────────────────────────────────

#[test]
fn adt_product_accessor_x() {
    let src = r#"
        (deftype Point [:Int x :Int y])
        (defn main [] (pure (x (Point 3 4))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 3);
}

#[test]
fn adt_product_accessor_y() {
    let src = r#"
        (deftype Point [:Int x :Int y])
        (defn main [] (pure (y (Point 3 4))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 4);
}

#[test]
fn adt_accessor_in_function() {
    let src = r#"
        (deftype Point [:Int x :Int y])
        (defn get-x [p] (x p))
        (defn main [] (pure (get-x (Point 3 4))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 3);
}

#[test]
fn adt_first_class_accessor() {
    let src = r#"
        (deftype Point [:Int x :Int y])
        (defn main [] (pure (let [f x] (f (Point 3 4)))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 3);
}

#[test]
fn adt_first_class_constructor() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (pure (let [f Some] (match (f 42) [None 0 (Some v) v]))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn adt_sum_accessor() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (defn main [] (pure (val (Some 42))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn repl_adt_accessor() {
    let mut r = ReplSession::new();
    r.typedef("(deftype Point [:Int x :Int y])").unwrap();
    assert_eq!(r.eval("(x (Point 3 4))").unwrap(), 3);
    assert_eq!(r.eval("(y (Point 3 4))").unwrap(), 4);
}

#[test]
fn repl_adt_first_class_accessor() {
    let mut r = ReplSession::new();
    r.typedef("(deftype Point [:Int x :Int y])").unwrap();
    assert_eq!(r.eval("(let [f x] (f (Point 5 6)))").unwrap(), 5);
}

// ── ADT: trait impl tests ─────────────────────────────────────────────

#[test]
fn adt_display_enum() {
    let src = r#"
        (deftype Color Red Green Blue)
        (impl Display Color
          (defn show [c]
            (match c
              [Red "Red"
               Green "Green"
               Blue "Blue"])))
        (defn main [] (print (show Green)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn adt_display_product() {
    let src = r#"
        (deftype Point [:Int x :Int y])
        (impl Display Point
          (defn show [p]
            (match p
              [(Point px py) (show px)])))
        (defn main [] (print (show (Point 42 0))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn adt_eq_enum() {
    let src = r#"
        (deftype Color Red Green Blue)
        (impl Eq Color
          (defn = [a b]
            (eq-i64 (match a [Red 0 Green 1 Blue 2])
                    (match b [Red 0 Green 1 Blue 2]))))
        (defn main []
          (if (= Red Red)
            (pure 1)
            (pure 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn adt_eq_enum_not_equal() {
    let src = r#"
        (deftype Color Red Green Blue)
        (impl Eq Color
          (defn = [a b]
            (eq-i64 (match a [Red 0 Green 1 Blue 2])
                    (match b [Red 0 Green 1 Blue 2]))))
        (defn main []
          (if (= Red Blue)
            (pure 1)
            (pure 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn repl_adt_display_enum() {
    let mut r = ReplSession::new();
    r.typedef("(deftype Color Red Green Blue)").unwrap();
    r.trait_impl(
        r#"(impl Display Color (defn show [c] (match c [Red "Red" Green "Green" Blue "Blue"])))"#,
    )
    .unwrap();
    assert_eq!(r.eval(r#"(print (show Red))"#).unwrap(), 0);
}

#[test]
fn repl_adt_eq_enum() {
    let mut r = ReplSession::new();
    r.typedef("(deftype Color Red Green Blue)").unwrap();
    r.trait_impl("(impl Eq Color (defn = [a b] (eq-i64 (match a [Red 0 Green 1 Blue 2]) (match b [Red 0 Green 1 Blue 2]))))").unwrap();
    assert_eq!(r.eval("(if (= Green Green) 1 0)").unwrap(), 1);
}

// ── ADT: polymorphic trait impl tests (Phase 1 — concrete instantiation) ──

#[test]
fn adt_display_option_int_batch() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (impl Display (Option Int)
          (defn show [self]
            (match self
              [None "None"
               (Some x) (show x)])))
        (defn main [] (print (show (Some 42))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn adt_display_option_int_none_batch() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (impl Display (Option Int)
          (defn show [self]
            (match self
              [None "None"
               (Some x) (show x)])))
        (defn main [] (print (show None)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn repl_adt_display_option_int() {
    let mut r = ReplSession::new();
    r.typedef("(deftype (Option a) None (Some [:a val]))")
        .unwrap();
    r.trait_impl(r#"(impl Display (Option Int) (defn show [self] (match self [None "None" (Some x) (show x)])))"#).unwrap();
    assert_eq!(r.eval(r#"(print (show (Some 42)))"#).unwrap(), 0);
    assert_eq!(r.eval(r#"(print (show None))"#).unwrap(), 0);
}

// ── ADT: polymorphic trait impl tests (Phase 2 — constrained polymorphism) ──

#[test]
fn adt_display_option_polymorphic_batch() {
    let src = r#"
        (deftype (Option a) None (Some [:a val]))
        (impl Display (Option :Display a)
          (defn show [self]
            (match self
              [None "None"
               (Some x) (show x)])))
        (defn main [] (print (show (Some 42))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn repl_adt_display_option_polymorphic() {
    let mut r = ReplSession::new();
    r.typedef("(deftype (Option a) None (Some [:a val]))")
        .unwrap();
    r.trait_impl(r#"(impl Display (Option :Display a) (defn show [self] (match self [None "None" (Some x) (show x)])))"#).unwrap();
    assert_eq!(r.eval(r#"(print (show (Some 42)))"#).unwrap(), 0);
}

// ── Parser tests for new impl target syntax ──

#[test]
fn parse_impl_target_bare() {
    let src = "(impl Display Int (defn show [x] x))";
    let prog = cranelisp::ast_builder::parse_program(src).unwrap();
    match &prog[0] {
        cranelisp::ast::TopLevel::TraitImpl(ti) => {
            assert_eq!(ti.target_type, "Int");
            assert!(ti.type_args.is_empty());
            assert!(ti.type_constraints.is_empty());
        }
        _ => panic!("expected TraitImpl"),
    }
}

#[test]
fn parse_impl_target_concrete_adt() {
    let src = "(impl Display (Option Int) (defn show [x] x))";
    let prog = cranelisp::ast_builder::parse_program(src).unwrap();
    match &prog[0] {
        cranelisp::ast::TopLevel::TraitImpl(ti) => {
            assert_eq!(ti.target_type, "Option");
            assert_eq!(ti.type_args, vec!["Int"]);
            assert!(ti.type_constraints.is_empty());
        }
        _ => panic!("expected TraitImpl"),
    }
}

#[test]
fn parse_impl_target_constrained_adt() {
    let src = "(impl Display (Option :Display a) (defn show [x] x))";
    let prog = cranelisp::ast_builder::parse_program(src).unwrap();
    match &prog[0] {
        cranelisp::ast::TopLevel::TraitImpl(ti) => {
            assert_eq!(ti.target_type, "Option");
            assert_eq!(ti.type_args, vec!["a"]);
            assert_eq!(
                ti.type_constraints,
                vec![("a".to_string(), "Display".to_string())]
            );
        }
        _ => panic!("expected TraitImpl"),
    }
}

// ── parse-int tests ──────────────────────────────────────────────────

#[test]
fn parse_int_valid() {
    let src = r#"
        (defn main []
          (pure (match (parse-int "42")
            [(Some n) n
             None -1])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn parse_int_invalid() {
    let src = r#"
        (defn main []
          (pure (match (parse-int "abc")
            [(Some n) n
             None -1])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, -1);
}

#[test]
fn parse_int_empty_string() {
    let src = r#"
        (defn main []
          (pure (match (parse-int "")
            [(Some n) n
             None -1])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, -1);
}

#[test]
fn parse_int_negative() {
    let src = r#"
        (defn main []
          (pure (match (parse-int "-7")
            [(Some n) n
             None 0])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, -7);
}

#[test]
fn parse_int_whitespace() {
    let src = r#"
        (defn main []
          (pure (match (parse-int "  123  ")
            [(Some n) n
             None 0])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 123);
}

#[test]
fn repl_parse_int() {
    let mut r = ReplSession::new();
    // parse-int "42" → Some 42
    let result = r
        .eval(r#"(match (parse-int "42") [(Some n) n None -1])"#)
        .unwrap();
    assert_eq!(result, 42);
    // parse-int "abc" → None
    let result = r
        .eval(r#"(match (parse-int "abc") [(Some n) n None -1])"#)
        .unwrap();
    assert_eq!(result, -1);
}

// ── bind! sugar tests ────────────────────────────────────────────────

#[test]
fn bind_bang_single_binding() {
    let src = r#"
        (defn main []
          (bind! [x (pure 42)]
            (pure x)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn bind_bang_multiple_bindings() {
    let src = r#"
        (defn main []
          (bind! [x (pure 10)
                 y (pure 20)]
            (pure (+ x y))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 30);
}

#[test]
fn bind_bang_with_print() {
    let src = r#"
        (defn main []
          (bind! [_ (print "hello")
                 _ (print "world")]
            (pure 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn repl_bind_bang() {
    // bind! is now a macro — REPL test helper doesn't expand macros, use bind directly
    let mut r = ReplSession::new();
    let result = r.eval("(bind (pure 42) (fn [x] (pure x)))").unwrap();
    assert_eq!(result, 42);
}

#[test]
fn parse_bind_bang_is_apply() {
    // bind! is now a macro, not parser sugar — parse_expr produces Apply
    let expr = cranelisp::ast_builder::parse_expr("(bind! [x (pure 1)] (pure x))").unwrap();
    match expr {
        Expr::Apply { callee, args, .. } => {
            match *callee {
                Expr::Var { ref name, .. } => assert_eq!(name, "bind!"),
                _ => panic!("expected Var callee"),
            }
            assert_eq!(args.len(), 2); // bindings bracket + body
        }
        _ => panic!("expected Apply from bind!, got: {:?}", expr),
    }
}

#[test]
fn parse_bind_bang_two_bindings_is_apply() {
    // bind! is now a macro, not parser sugar — parse_expr produces Apply
    let expr =
        cranelisp::ast_builder::parse_expr("(bind! [x (pure 1) y (pure 2)] (pure x))").unwrap();
    match expr {
        Expr::Apply { callee, args, .. } => {
            match *callee {
                Expr::Var { ref name, .. } => assert_eq!(name, "bind!"),
                _ => panic!("expected Var callee"),
            }
            assert_eq!(args.len(), 2); // bindings bracket + body
        }
        _ => panic!("expected Apply from bind!, got: {:?}", expr),
    }
}

// ── List type tests ─────────────────────────────────────────────────

#[test]
fn list_construction() {
    let src = r#"
        (defn main []
          (pure (match (Cons 1 (Cons 2 Nil))
            [(Cons h t) h
             Nil 0])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn list_sugar() {
    let src = r#"
        (defn main []
          (pure (match (list 1 2 3)
            [(Cons h t) h
             Nil 0])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn list_sugar_empty() {
    let src = r#"
        (defn main []
          (pure (match (list)
            [Nil 99
             _ 0])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 99);
}

#[test]
fn list_nil_check() {
    let src = r#"
        (defn main []
          (pure (if (empty? (list)) 1 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn list_non_empty_check() {
    let src = r#"
        (defn main []
          (pure (if (empty? (list 1 2 3)) 1 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn list_head_tail() {
    let src = r#"
        (defn main []
          (pure (+ (head (list 42 99))
                   (head (tail (list 1 2 3))))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 44); // 42 + 2
}

#[test]
fn list_nested() {
    // Nested lists: (list (list 1 2) (list 3 4))
    let src = r#"
        (defn main []
          (pure (head (head (list (list 10 20) (list 30 40))))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 10);
}

#[test]
fn list_recursive_function() {
    let src = r#"
        (defn length [xs]
          (if (empty? xs)
            0
            (+ 1 (length (tail xs)))))
        (defn main [] (pure (length (list 1 2 3 4 5))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 5);
}

#[test]
fn list_example() {
    // Verifies the full examples/list.cl program runs
    let src = r#"
        (defn length [xs]
          (if (empty? xs)
            0
            (+ 1 (length (tail xs)))))
        (defn main []
          (do
            (print (show (empty? (list))))
            (print (show (empty? (list 1 2 3))))
            (print (show (head (list 42 99))))
            (print (show (head (tail (list 1 2 3)))))
            (print (show (length (list 1 2 3 4 5))))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0); // last print returns 0
}

#[test]
fn repl_list_sugar() {
    // list is now a macro — REPL test helper doesn't expand macros, use Cons/Nil
    let mut r = ReplSession::new();
    let result = r.eval("(head (Cons 10 (Cons 20 (Cons 30 Nil))))").unwrap();
    assert_eq!(result, 10);
}

#[test]
fn repl_list_empty() {
    // list is now a macro — REPL test helper doesn't expand macros, use Cons/Nil
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(empty? Nil)").unwrap(), 1); // true
    assert_eq!(r.eval("(empty? (Cons 1 Nil))").unwrap(), 0); // false
}

#[test]
fn repl_list_head_tail() {
    // list is now a macro — REPL test helper doesn't expand macros, use Cons/Nil
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(head (Cons 42 (Cons 99 Nil)))").unwrap(), 42);
    assert_eq!(
        r.eval("(head (tail (Cons 1 (Cons 2 (Cons 3 Nil)))))")
            .unwrap(),
        2
    );
}

#[test]
fn repl_list_recursive() {
    // list is now a macro — REPL test helper doesn't expand macros, use Cons/Nil
    let mut r = ReplSession::new();
    r.defn("(defn length [xs] (if (empty? xs) 0 (+ 1 (length (tail xs)))))")
        .unwrap();
    assert_eq!(
        r.eval("(length (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil))))))")
            .unwrap(),
        5
    );
    assert_eq!(r.eval("(length Nil)").unwrap(), 0);
}

// ── TypeExpr::Applied parsing tests ─────────────────────────────────

#[test]
fn parse_applied_type_expr() {
    // Test that :(List a) parses as TypeExpr::Applied in a deftype field
    let src = "(deftype (List a) Nil (Cons [:a head :(List a) tail]))";
    let prog = parse_program(src).unwrap();
    match &prog[0] {
        cranelisp::ast::TopLevel::TypeDef {
            name,
            type_params,
            constructors,
            ..
        } => {
            assert_eq!(name, "List");
            assert_eq!(type_params, &["a"]);
            assert_eq!(constructors.len(), 2);
            assert_eq!(constructors[0].name, "Nil");
            assert_eq!(constructors[1].name, "Cons");
            assert_eq!(constructors[1].fields.len(), 2);
            // The tail field should have Applied type
            match &constructors[1].fields[1].type_expr {
                cranelisp::ast::TypeExpr::Applied(name, args) => {
                    assert_eq!(name, "List");
                    assert_eq!(args.len(), 1);
                }
                other => panic!("expected Applied, got {:?}", other),
            }
        }
        _ => panic!("expected TypeDef"),
    }
}

#[test]
fn parse_applied_type_concrete() {
    // :(Option Int) should parse as Applied in a field definition
    let src = "(deftype Wrapper [:(Option Int) inner])";
    let prog = parse_program(src).unwrap();
    match &prog[0] {
        cranelisp::ast::TopLevel::TypeDef { constructors, .. } => {
            assert_eq!(constructors.len(), 1);
            assert_eq!(constructors[0].fields.len(), 1);
            match &constructors[0].fields[0].type_expr {
                cranelisp::ast::TypeExpr::Applied(name, args) => {
                    assert_eq!(name, "Option");
                    assert_eq!(args.len(), 1);
                    match &args[0] {
                        cranelisp::ast::TypeExpr::Named(n) => assert_eq!(n, "Int"),
                        other => panic!("expected Named(Int), got {:?}", other),
                    }
                }
                other => panic!("expected Applied, got {:?}", other),
            }
        }
        _ => panic!("expected TypeDef"),
    }
}

// ── Prelude Option available by default tests ───────────────────────

#[test]
fn prelude_option_some() {
    let src = r#"
        (defn main []
          (pure (match (Some 42)
            [(Some n) n
             None 0])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn prelude_option_none() {
    let src = r#"
        (defn main []
          (pure (match None
            [(Some n) n
             None 99])))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 99);
}

#[test]
fn repl_prelude_option() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(match (Some 42) [(Some n) n None 0])").unwrap(), 42);
    assert_eq!(r.eval("(match None [(Some n) n None 99])").unwrap(), 99);
}

// ── Vec type tests ──────────────────────────────────────────────────

#[test]
fn vec_len_literal() {
    let src = r#"
        (defn main [] (pure (vec-len [1 2 3])))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn vec_len_empty() {
    let src = r#"
        (defn main [] (pure (vec-len [])))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 0);
}

#[test]
fn vec_get_elements() {
    let src = r#"
        (defn main [] (pure (vec-get [10 20 30] 1)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 20);
}

#[test]
fn vec_set_returns_new() {
    let src = r#"
        (defn main [] (pure (vec-get (vec-set [10 20 30] 1 99) 1)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 99);
}

#[test]
fn vec_push_appends() {
    let src = r#"
        (defn main [] (pure (vec-len (vec-push [1 2] 3))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn vec_push_value() {
    let src = r#"
        (defn main [] (pure (vec-get (vec-push [10 20] 30) 2)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 30);
}

#[test]
fn vec_sugar_equivalent() {
    let src = r#"
        (defn main [] (pure (vec-len (vec 4 5 6 7))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 4);
}

#[test]
fn vec_in_let() {
    let src = r#"
        (defn main []
          (let [xs [1 2 3 4 5]]
            (pure (vec-get xs 4))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 5);
}

#[test]
fn vec_cow_safety_set() {
    // vec-set must not mutate the original
    let src = r#"
        (defn main []
          (let [xs [1 2 3]]
            (let [ys (vec-set xs 0 99)]
              (pure (vec-get xs 0)))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 1);
}

#[test]
fn vec_cow_safety_push() {
    // vec-push must not mutate the original
    let src = r#"
        (defn main []
          (let [xs [1 2]]
            (let [ys (vec-push xs 3)]
              (pure (vec-len xs)))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 2);
}

#[test]
fn vec_cow_safety_independence() {
    // returned vec must be independent
    let src = r#"
        (defn main []
          (let [xs [10 20 30]]
            (let [ys (vec-set xs 1 99)]
              (pure (+ (vec-get xs 1) (vec-get ys 1))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 119); // 20 + 99
}

#[test]
fn vec_nested_access() {
    let src = r#"
        (defn main []
          (pure (vec-get (vec-get [[1 2] [3 4]] 1) 0)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn vec_push_empty() {
    let src = r#"
        (defn main []
          (let [xs (vec-push [] 42)]
            (pure (vec-get xs 0))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 42);
}

#[test]
fn vec_with_booleans() {
    let src = r#"
        (defn main []
          (pure (vec-len [true false true])))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn vec_example_file() {
    // Tests the same logic as examples/vec.cl: output is 5, 3, 6, returns 99
    let src = r#"
        (defn main []
          (let [xs [1 2 3 4 5]]
            (do
              (print (show (vec-len xs)))
              (print (show (vec-get xs 2)))
              (let [ys (vec-push xs 6)]
                (do
                  (print (show (vec-len ys)))
                  (let [zs (vec-set ys 0 99)]
                    (pure (vec-get zs 0))))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 99);
}

#[test]
fn repl_vec_literal() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(vec-len [1 2 3])").unwrap(), 3);
}

#[test]
fn repl_vec_get() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(vec-get [10 20 30] 1)").unwrap(), 20);
}

#[test]
fn repl_vec_set() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(vec-get (vec-set [10 20 30] 1 99) 1)").unwrap(), 99);
}

#[test]
fn repl_vec_push() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(vec-len (vec-push [1 2] 3))").unwrap(), 3);
}

#[test]
fn repl_vec_empty() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(vec-len [])").unwrap(), 0);
}

#[test]
fn repl_vec_push_empty() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(vec-get (vec-push [] 42) 0)").unwrap(), 42);
}

// --- vec-map tests ---

#[test]
fn vec_map_lambda() {
    let src = r#"
        (defn main [] (pure (vec-get (vec-map (fn [x] (* x x)) [1 2 3 4]) 2)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 9);
}

#[test]
fn vec_map_named_fn() {
    let src = r#"
        (defn double [x] (* x 2))
        (defn main [] (pure (vec-get (vec-map double [10 20 30]) 1)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 40);
}

#[test]
fn vec_map_empty() {
    let src = r#"
        (defn main [] (pure (vec-len (vec-map (fn [x] (* x x)) []))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 0);
}

#[test]
fn vec_map_preserves_len() {
    let src = r#"
        (defn main [] (pure (vec-len (vec-map (fn [x] (+ x 1)) [1 2 3 4 5]))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 5);
}

// --- vec-reduce tests ---

#[test]
fn vec_reduce_lambda() {
    let src = r#"
        (defn main [] (pure (vec-reduce (fn [acc x] (+ acc x)) 0 [1 2 3 4])))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 10);
}

#[test]
fn vec_reduce_operator() {
    let src = r#"
        (defn main [] (pure (vec-reduce + 0 [1 2 3 4 5])))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 15);
}

#[test]
fn vec_reduce_empty() {
    let src = r#"
        (defn main [] (pure (vec-reduce + 0 [])))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 0);
}

#[test]
fn vec_reduce_multiply() {
    let src = r#"
        (defn main [] (pure (vec-reduce * 1 [1 2 3 4 5])))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 120);
}

// --- list fmap tests ---

#[test]
fn list_fmap_lambda() {
    let src = r#"
        (defn main [] (pure (head (fmap (fn [x] (* x 10)) (list 3 2 1)))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 30);
}

#[test]
fn list_fmap_named_fn() {
    let src = r#"
        (defn double [x] (* x 2))
        (defn main [] (pure (head (tail (fmap double (list 5 10 15))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 20);
}

#[test]
fn list_fmap_empty() {
    let src = r#"
        (defn main [] (pure (if (empty? (fmap (fn [x] x) (list))) 1 0)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 1);
}

// --- list-reduce tests ---

#[test]
fn list_reduce_lambda() {
    let src = r#"
        (defn main [] (pure (list-reduce (fn [acc x] (+ acc x)) 0 (list 1 2 3))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 6);
}

#[test]
fn list_reduce_operator() {
    let src = r#"
        (defn main [] (pure (list-reduce + 0 (list 1 2 3 4 5))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 15);
}

#[test]
fn list_reduce_empty() {
    let src = r#"
        (defn main [] (pure (list-reduce + 0 (list))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 0);
}

#[test]
fn list_reduce_multiply() {
    let src = r#"
        (defn main [] (pure (list-reduce * 1 (list 1 2 3 4 5))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 120);
}

// --- composition tests ---

#[test]
fn vec_reduce_of_vec_map() {
    let src = r#"
        (defn main []
          (pure (vec-reduce + 0 (vec-map (fn [x] (* x x)) [1 2 3]))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 14); // 1 + 4 + 9
}

#[test]
fn list_reduce_of_list_fmap() {
    let src = r#"
        (defn main []
          (pure (list-reduce + 0 (fmap (fn [x] (* x x)) (list 1 2 3)))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 14); // 1 + 4 + 9
}

// ── Type annotation tests ───────────────────────────────────────────

#[test]
fn annotation_expr_int() {
    let src = r#"(defn main [] (pure :Int 42))"#;
    assert_eq!(compile_and_run(src).unwrap(), 42);
}

#[test]
fn annotation_constrains_none_to_option_int() {
    let src = r#"
        (defn main []
          (let [x :(Option Int) None]
            (match x
              [None (pure 1)
               (Some v) (pure v)])))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 1);
}

#[test]
fn annotation_param_concrete() {
    let src = r#"
        (defn f [:Int x] (+ x 1))
        (defn main [] (pure (f 41)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 42);
}

#[test]
fn annotation_param_trait_constraint() {
    // :Num annotation on params makes it constrained polymorphic
    let src = r#"
        (defn add [:Num x :Num y] (+ x y))
        (defn main [] (pure (add 1 2)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn annotation_param_trait_both_types() {
    let src = r#"
        (defn add [:Num x :Num y] (+ x y))
        (defn main [] (do (print (show (add 1.5 2.5))) (pure (add 1 2))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn repl_annotation_expr() {
    let mut r = ReplSession::new();
    let result = r.eval(":Int 42").unwrap();
    assert_eq!(result, 42);
}

#[test]
fn repl_annotation_option_int() {
    let mut r = ReplSession::new();
    let result = r.eval(":(Option Int) None").unwrap();
    // None is tag 0
    assert_eq!(result, 0);
}

#[test]
fn repl_annotation_param_defn() {
    let mut r = ReplSession::new();
    r.defn("(defn f [:Int x] (+ x 1))").unwrap();
    let result = r.eval("(f 41)").unwrap();
    assert_eq!(result, 42);
}

#[test]
fn repl_annotation_trait_constraint() {
    let mut r = ReplSession::new();
    r.defn("(defn add [:Num x :Num y] (+ x y))").unwrap();
    let result = r.eval("(add 1 2)").unwrap();
    assert_eq!(result, 3);
}

#[test]
fn repl_annotation_trait_constraint_float() {
    let mut r = ReplSession::new();
    r.defn("(defn add [:Num x :Num y] (+ x y))").unwrap();
    let result = r.eval("(add 1.5 2.5)").unwrap();
    let f = f64::from_bits(result as u64);
    assert!((f - 4.0).abs() < 1e-10);
}

#[test]
fn repl_annotated_lambda() {
    let mut r = ReplSession::new();
    let result = r.eval("((fn [:Int x] (+ x 1)) 41)").unwrap();
    assert_eq!(result, 42);
}

// ── Lazy Seq tests ──────────────────────────────────────────────────

#[test]
fn seq_to_list_take_range() {
    let src = r#"
        (defn sum-list [xs]
          (list-reduce + 0 xs))
        (defn main [] (pure (sum-list (to-list (lazy-take 5 (range-from 0))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 10); // 0+1+2+3+4
}

#[test]
fn seq_fmap_take() {
    let src = r#"
        (defn main [] (pure (head (to-list (lazy-take 3 (fmap inc (range-from 10)))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 11);
}

#[test]
fn seq_lazy_reduce() {
    let src = r#"
        (defn main [] (pure (lazy-reduce + 0 (lazy-take 5 (range-from 1)))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 15);
}

#[test]
fn seq_iterate() {
    let src = r#"
        (defn main [] (pure (head (to-list (lazy-take 1 (lazy-drop 5 (iterate (fn [x] (* x 2)) 1)))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 32); // 2^5
}

#[test]
fn seq_lazy_filter() {
    let src = r#"
        (defn main []
          (pure (head (to-list (lazy-take 3
            (lazy-filter (fn [x] (> x 2)) (range-from 0)))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn seq_repeat() {
    let src = r#"
        (defn main [] (pure (lazy-reduce + 0 (lazy-take 3 (repeat 42)))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 126); // 42*3
}

#[test]
fn seq_to_list_finite() {
    let src = r#"
        (defn main [] (pure (head (tail (to-list (lazy-take 5 (range-from 0)))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 1);
}

#[test]
fn seq_lazy_drop() {
    let src = r#"
        (defn main [] (pure (head (to-list (lazy-take 3 (lazy-drop 3 (range-from 0)))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

// ── Multi-sig dispatch tests (Seq) ─────────────────────────────────

#[test]
fn multisig_reduce_vec() {
    let src = r#"
        (defn main [] (pure (reduce + 0 [1 2 3])))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 6);
}

#[test]
fn multisig_reduce_list() {
    let src = r#"
        (defn main [] (pure (reduce + 0 (list 1 2 3))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 6);
}

#[test]
fn multisig_reduce_seq() {
    let src = r#"
        (defn main [] (pure (reduce + 0 (lazy-take 5 (range-from 1)))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 15);
}

#[test]
fn multisig_map_vec_to_seq() {
    let src = r#"
        (defn main [] (pure (head (to-list (map inc [1 2 3])))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 2);
}

#[test]
fn multisig_map_list_to_seq() {
    let src = r#"
        (defn main [] (pure (head (to-list (map inc (list 1 2 3))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 2);
}

#[test]
fn multisig_take_vec() {
    let src = r#"
        (defn main [] (pure (lazy-reduce + 0 (take 2 [10 20 30]))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 30);
}

#[test]
fn multisig_take_list() {
    let src = r#"
        (defn main [] (pure (lazy-reduce + 0 (take 2 (list 10 20 30)))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 30);
}

#[test]
fn multisig_take_seq() {
    let src = r#"
        (defn main [] (pure (lazy-reduce + 0 (take 5 (range-from 1)))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 15);
}

#[test]
fn multisig_filter_vec() {
    let src = r#"
        (defn main [] (pure (head (to-list (filter (fn [x] (> x 2)) [1 2 3 4 5])))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn multisig_filter_list() {
    let src = r#"
        (defn main [] (pure (head (to-list (filter (fn [x] (> x 2)) (list 1 2 3 4 5))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn multisig_drop_vec() {
    let src = r#"
        (defn main [] (pure (head (to-list (drop 3 [10 20 30 40 50])))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 40);
}

#[test]
fn multisig_drop_list() {
    let src = r#"
        (defn main [] (pure (head (to-list (drop 3 (list 10 20 30 40 50))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 40);
}

#[test]
fn multisig_drop_seq() {
    let src = r#"
        (defn main [] (pure (head (to-list (lazy-take 1 (drop 3 (lazy-take 6 (range-from 0))))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn seq_pipeline_fmap_filter_take_reduce() {
    // Full lazy pipeline: range → fmap → filter → take → reduce
    let src = r#"
        (defn main []
          (pure (lazy-reduce + 0
            (lazy-take 3
              (lazy-filter (fn [x] (> x 5))
                (fmap (fn [x] (* x 2)) (range-from 1)))))))
    "#;
    // range: 1,2,3,4,5,6,...  fmap *2: 2,4,6,8,10,12,...  filter >5: 6,8,10,...  take 3: 6,8,10
    assert_eq!(compile_and_run(src).unwrap(), 24);
}

#[test]
fn seq_example_file() {
    // Verifies examples/seq.cl produces correct output
    let src = r#"
        (defn main []
          (do
            (print (show (head (to-list (take 5 (range-from 0))))))
            (print (show (head (to-list (take 3 (map inc (range-from 10)))))))
            (print (show :Int (reduce + 0 (lazy-take 5 (range-from 1)))))
            (print (show (head (to-list (lazy-drop 5 (lazy-take 10 (iterate (fn [x] (* x 2)) 1)))))))
            (print (show (head (to-list (filter (fn [x] (> x 2)) [1 2 3 4 5])))))
            (print (show (head (to-list (lazy-take 3 (repeat 42))))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 0); // last print returns 0
}

// ── REPL Seq tests ─────────────────────────────────────────────────

#[test]
fn repl_seq_lazy_take_range() {
    let mut r = ReplSession::new();
    assert_eq!(
        r.eval("(lazy-reduce + 0 (lazy-take 5 (range-from 1)))")
            .unwrap(),
        15
    );
}

#[test]
fn repl_seq_to_list() {
    let mut r = ReplSession::new();
    assert_eq!(
        r.eval("(head (to-list (lazy-take 3 (range-from 10))))")
            .unwrap(),
        10
    );
}

#[test]
fn repl_seq_iterate() {
    let mut r = ReplSession::new();
    // iterate doubling from 1, take first = 1
    assert_eq!(
        r.eval("(head (to-list (lazy-take 1 (iterate (fn [x] (* x 2)) 1))))")
            .unwrap(),
        1
    );
}

#[test]
fn repl_seq_filter() {
    let mut r = ReplSession::new();
    assert_eq!(
        r.eval("(head (to-list (lazy-take 1 (lazy-filter (fn [x] (> x 3)) (range-from 0)))))")
            .unwrap(),
        4
    );
}

#[test]
fn repl_seq_repeat() {
    let mut r = ReplSession::new();
    assert_eq!(
        r.eval("(lazy-reduce + 0 (lazy-take 4 (repeat 10)))")
            .unwrap(),
        40
    );
}

#[test]
fn repl_multisig_reduce_vec() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(reduce + 0 [1 2 3 4])").unwrap(), 10);
}

#[test]
fn repl_multisig_reduce_list() {
    // list is now a macro — REPL test helper doesn't expand macros, use Cons/Nil
    let mut r = ReplSession::new();
    assert_eq!(
        r.eval("(reduce + 0 (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil)))))")
            .unwrap(),
        10
    );
}

#[test]
fn repl_multisig_map_vec() {
    let mut r = ReplSession::new();
    assert_eq!(r.eval("(head (to-list (map inc [10 20 30])))").unwrap(), 11);
}

#[test]
fn repl_multisig_map_list() {
    // list is now a macro — REPL test helper doesn't expand macros, use Cons/Nil
    let mut r = ReplSession::new();
    assert_eq!(
        r.eval("(head (to-list (map inc (Cons 10 (Cons 20 (Cons 30 Nil))))))")
            .unwrap(),
        11
    );
}

// ── REPL: symbol display tests ────────────────────────────────────────

#[test]
fn repl_user_fn_bare_name_describes() {
    let mut r = ReplSession::new();
    r.defn("(defn foo [x] x)").unwrap();
    match r.tc.describe_symbol("foo") {
        Some(SymbolInfo::UserFn { scheme }) => {
            assert!(matches!(scheme.ty, Type::Fn(_, _)));
        }
        other => panic!("expected UserFn, got {:?}", other.is_some()),
    }
}

#[test]
fn repl_prelude_fn_bare_name_describes() {
    let r = ReplSession::new();
    match r.tc.describe_symbol("empty?") {
        Some(SymbolInfo::UserFn { scheme }) => {
            assert!(matches!(scheme.ty, Type::Fn(_, _)));
        }
        other => panic!("expected UserFn for empty?, got {:?}", other.is_some()),
    }
}

// Reference counting tests are in tests/rc.rs (separate binary, runs single-threaded
// to avoid global counter interference from concurrent tests).

// ===== TCO (Tail Call Optimization) tests =====

#[test]
fn tco_deep_countdown() {
    // 1M iterations — would overflow the stack without TCO
    let src = r#"
        (defn countdown [n]
          (if (= n 0)
            0
            (countdown (- n 1))))
        (defn main [] (pure (countdown 1000000)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn tco_accumulator() {
    // Tail-recursive sum with accumulator — 1M iterations
    let src = r#"
        (defn sum-to [acc n]
          (if (= n 0)
            acc
            (sum-to (+ acc n) (- n 1))))
        (defn main [] (pure (sum-to 0 1000000)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 500000500000);
}

#[test]
fn tco_match_tail_position() {
    // Tail call inside match arm
    let src = r#"
        (defn list-len [acc xs]
          (match xs
            [Nil acc
             (Cons h t) (list-len (+ acc 1) t)]))
        (defn main []
          (pure (list-len 0 (list 1 2 3 4 5))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 5);
}

#[test]
fn tco_let_body_tail_position() {
    // Tail call inside let body
    let src = r#"
        (defn loop-down [n]
          (if (= n 0)
            42
            (let [m (- n 1)]
              (loop-down m))))
        (defn main [] (pure (loop-down 1000000)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 42);
}

#[test]
fn tco_do_last_expr_tail_position() {
    // Tail call as last expression in do
    let src = r#"
        (defn count-print [n]
          (if (= n 0)
            (pure 0)
            (do
              (print (show n))
              (count-print (- n 1)))))
        (defn main [] (count-print 3))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn tco_non_tail_recursion_unchanged() {
    // Non-tail recursion (factorial) still works correctly
    let src = r#"
        (defn fact [n]
          (if (= n 0)
            1
            (* n (fact (- n 1)))))
        (defn main [] (pure (fact 12)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 479001600);
}

#[test]
fn tco_list_reduce_large() {
    // list-reduce (from prelude) on a moderately large list
    // This is tail-recursive and should benefit from TCO
    let src = r#"
        (defn build-list [acc n]
          (if (= n 0)
            acc
            (build-list (Cons n acc) (- n 1))))
        (defn main []
          (pure (reduce + 0 (build-list Nil 10000))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 50005000);
}

// ──── Functor (HKT) tests ────

#[test]
fn functor_fmap_option_some() {
    let src = r#"
        (defn main [] (pure (val (fmap inc (Some 5)))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 6);
}

#[test]
fn functor_fmap_option_none() {
    let src = r#"
        (defn is-some [opt]
          (match opt
            [None false
             (Some _) true]))
        (defn main [] (pure (if (is-some (fmap inc None)) 1 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn functor_fmap_list() {
    let src = r#"
        (defn main []
          (pure (head (fmap inc (list 10 20 30)))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 11);
}

#[test]
fn functor_fmap_list_all_elements() {
    let src = r#"
        (defn sum-list [xs]
          (match xs
            [Nil 0
             (Cons h t) (+ h (sum-list t))]))
        (defn main []
          (pure (sum-list (fmap inc (list 1 2 3)))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 9); // (2 + 3 + 4)
}

#[test]
fn functor_fmap_list_empty() {
    let src = r#"
        (defn main []
          (pure (if (empty? (fmap inc Nil)) 1 0)))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn functor_fmap_with_lambda() {
    let src = r#"
        (defn main []
          (pure (val (fmap (fn [x] (* x 10)) (Some 7)))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 70);
}

#[test]
fn functor_fmap_composition() {
    // fmap f . fmap g = fmap (f . g) — test by chaining
    let src = r#"
        (defn double [:Int x] (* x 2))
        (defn main []
          (pure (val (fmap inc (fmap double (Some 3))))))
    "#;
    let result = compile_and_run(src).unwrap();
    assert_eq!(result, 7); // double 3 = 6, inc 6 = 7
}

#[test]
fn functor_fmap_seq_basic() {
    let src = r#"
        (defn main []
          (pure (head (to-list (fmap inc (SeqCons 1 (fn [] (SeqCons 2 (fn [] SeqNil)))))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 2);
}

#[test]
fn functor_fmap_seq_empty() {
    let src = r#"
        (defn main []
          (pure (if (empty? (to-list (fmap inc SeqNil))) 1 0)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 1);
}

#[test]
fn functor_fmap_seq_with_range() {
    // fmap inc on range-from 10, take 3, reduce sum = 11+12+13 = 36
    let src = r#"
        (defn main []
          (pure (lazy-reduce + 0 (lazy-take 3 (fmap inc (range-from 10))))))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 36);
}

#[test]
fn functor_hkt_arity_error() {
    // Int is not a type constructor — should fail
    let src = r#"
        (deftrait (BadFunctor f)
          (bfmap [(Fn [a] b) (f a)] (f b)))
        (impl BadFunctor Int
          (defn bfmap [f x] x))
        (defn main [] (pure 0))
    "#;
    let result = compile_and_run(src);
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(err_msg.contains("not a type constructor"));
}

// ── /sexp and /ast introspection tests ─────────────────────────────────
// These test the real REPL prelude loading which captures sexp/defn/source.

fn real_repl_session() -> cranelisp::repl::ReplSession {
    let mut s = cranelisp::repl::ReplSession::new().unwrap();
    s.load_prelude();
    s
}

#[test]
fn repl_sexp_prelude_defn() {
    let r = real_repl_session();
    let view = r
        .tc
        .get_def_codegen("list-reduce")
        .expect("list-reduce should exist");
    assert!(view.sexp.is_some(), "prelude defn should have sexp");
    assert!(view.defn.is_some(), "prelude defn should have defn");
    assert!(view.source.is_some(), "prelude defn should have source");
    let sexp_str = format!("{}", view.sexp.as_ref().unwrap());
    assert!(
        sexp_str.starts_with("(defn"),
        "sexp should start with (defn, got: {}",
        sexp_str
    );
    let ast_str = format!("{}", view.defn.as_ref().unwrap());
    assert!(
        ast_str.starts_with("Defn"),
        "ast should start with Defn, got: {}",
        ast_str
    );
}

#[test]
fn repl_sexp_prelude_multisig() {
    let r = real_repl_session();
    let specs = r.tc.find_specializations("reduce");
    assert!(!specs.is_empty(), "reduce should have specializations");
    // At least some specializations should have codegen artifacts
    let compiled: Vec<_> = specs.iter().filter(|(_, v)| v.got_slot.is_some()).collect();
    assert!(
        compiled.len() >= 2,
        "expected at least 2 compiled reduce specializations, got {}",
        compiled.len()
    );
    for (mangled, view) in &compiled {
        assert!(view.sexp.is_some(), "{} should have sexp", mangled);
        assert!(view.defn.is_some(), "{} should have defn", mangled);
    }
}

#[test]
fn repl_sexp_prelude_trait_impl() {
    let r = real_repl_session();
    let view = r.tc.get_def_codegen("show$Int").expect("show$Int should exist");
    assert!(view.sexp.is_some(), "trait impl method should have sexp");
    assert!(view.defn.is_some(), "trait impl method should have defn");
}

#[test]
fn repl_sexp_prelude_source() {
    let r = real_repl_session();
    let view = r
        .tc
        .get_def_codegen("list-reduce")
        .expect("list-reduce should exist");
    let source = view.source.as_ref().expect("should have source");
    assert!(
        source.contains("defn list-reduce"),
        "source should contain original text"
    );
}

// ── Macro integration tests ──────────────────────────────────────────

/// Compile and run source that may contain defmacro forms.
/// Handles begin flattening and defmacro-in-results.
fn compile_and_run_with_macros(src: &str) -> Result<i64, CranelispError> {
    let prelude = parse_program(PRELUDE)?;
    let user_sexps = parse_sexps(src)?;
    let user_sexps = strip_module_decls(user_sexps);
    let has_macros = user_sexps.iter().any(is_defmacro);

    // Always create macro session for prelude macros (list, bind!)
    let mut macro_session = cranelisp::repl::ReplSession::new()?;
    macro_session.load_prelude();

    // Compile user defmacros if any
    if has_macros {
        for sexp in &user_sexps {
            if is_defmacro(sexp) {
                let info = parse_defmacro(sexp)?;
                let ptr = compile_macro(
                    &mut macro_session.tc,
                    &mut macro_session.jit,
                    &info,
                    Some(&macro_session.macro_env),
                )?;
                macro_session.macro_env.register(
                    info.name,
                    ptr,
                    info.docstring,
                    info.fixed_params,
                    info.rest_param,
                    Some(info.body_sexp),
                );
            }
        }
    }

    // Expand all user code, flatten begin forms, handle defmacro-in-results
    let mut final_sexps = Vec::new();
    for sexp in user_sexps {
        if is_defmacro(&sexp) {
            continue; // already compiled above
        }
        let expanded = expand_sexp(sexp, &macro_session.macro_env, 0)?;
        let forms = flatten_begin(expanded);
        for form in forms {
            if is_defmacro(&form) {
                let info = parse_defmacro(&form)?;
                let ptr = compile_macro(
                    &mut macro_session.tc,
                    &mut macro_session.jit,
                    &info,
                    Some(&macro_session.macro_env),
                )?;
                macro_session.macro_env.register(
                    info.name,
                    ptr,
                    info.docstring,
                    info.fixed_params,
                    info.rest_param,
                    Some(info.body_sexp),
                );
            } else {
                final_sexps.push(form);
            }
        }
    }

    // Re-expand for bare-symbol expansion of newly registered macros
    let expanded = expand_sexps(final_sexps, &macro_session.macro_env)?;
    let user = build_program(&expanded)?;

    let program: Vec<_> = prelude.into_iter().chain(user).collect();
    let mut tc = TypeChecker::new();
    let mut jit = Jit::new()?;
    try_load_stdio_platform(&mut jit, &mut tc);
    let result = tc.check_program(&program)?;
    let multi_defns = tc.build_multi_defns(&program);
    jit.populate_builtin_func_ids(&mut tc.modules);
    let raw = jit.compile_and_run(&program, &multi_defns, &result, &tc)?;
    Ok(unwrap_io_val(raw))
}

#[test]
fn macro_identity() {
    let src = r#"
        (defmacro identity [x] x)
        (defn main [] (pure (identity 42)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_constant_constructor() {
    let src = r#"
        (defmacro always-42 [] (SexpInt 42))
        (defn main [] (pure (always-42)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_sexp_building() {
    // Macro that builds (+ x 1)
    let src = r#"
        (defmacro my-inc [x]
          (SexpList (slist (SexpSym "+") x (SexpInt 1))))
        (defn main [] (pure (my-inc 41)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_two_params() {
    // Macro that builds (if cond body 0)
    let src = r#"
        (defmacro my-when [cond body]
          (SexpList (slist (SexpSym "if") cond body (SexpInt 0))))
        (defn main [] (pure (my-when true 42)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_two_params_false_branch() {
    let src = r#"
        (defmacro my-when [cond body]
          (SexpList (slist (SexpSym "if") cond body (SexpInt 0))))
        (defn main [] (pure (my-when false 42)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 0);
}

#[test]
fn macro_variadic() {
    // Variadic macro that returns the first argument
    let src = r#"
        (defmacro first-of [& args] (shead args))
        (defn main [] (pure (first-of 42 99)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_chained() {
    // Second macro uses first macro's expansion
    let src = r#"
        (defmacro my-inc [x]
          (SexpList (slist (SexpSym "+") x (SexpInt 1))))
        (defmacro my-add2 [x]
          (SexpList (slist (SexpSym "my-inc") (SexpList (slist (SexpSym "my-inc") x)))))
        (defn main [] (pure (my-add2 40)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_with_string_arg() {
    let src = r#"
        (defmacro my-inc [x]
          (SexpList (slist (SexpSym "+") x (SexpInt 1))))
        (defn main []
          (do
            (print (show (my-inc 41)))
            (pure 0)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 0);
}

#[test]
fn macro_no_macros_fast_path() {
    // No macros — should still work via the fast path
    let src = r#"
        (defn main [] (pure (+ 40 2)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_expansion_depth_limit() {
    // Macro that expands infinitely
    let src = r#"
        (defmacro loop-forever [x]
          (SexpList (slist (SexpSym "loop-forever") x)))
        (defn main [] (pure (loop-forever 1)))
    "#;
    let err = compile_and_run_with_macros(src).unwrap_err();
    match err {
        CranelispError::ParseError { message, .. } => {
            assert!(
                message.contains("expansion depth limit"),
                "got: {}",
                message
            );
        }
        _ => panic!("expected ParseError, got: {:?}", err),
    }
}

#[test]
fn macro_repl_compile_and_register() {
    use cranelisp::macro_expand::{compile_macro, parse_defmacro};
    use cranelisp::sexp::parse_sexp;

    let mut r = real_repl_session();
    let sexp = parse_sexp("(defmacro my-inc [x] (SexpList (slist (SexpSym \"+\") x (SexpInt 1))))")
        .unwrap();
    let info = parse_defmacro(&sexp).unwrap();
    let ptr = compile_macro(&mut r.tc, &mut r.jit, &info, Some(&r.macro_env)).unwrap();
    r.macro_env.register(
        info.name.clone(),
        ptr,
        info.docstring.clone(),
        info.fixed_params.clone(),
        info.rest_param.clone(),
        Some(info.body_sexp.clone()),
    );
    assert!(!r.macro_env.is_empty());
}

#[test]
fn macro_repl_expand_sexp() {
    use cranelisp::macro_expand::{compile_macro, expand_sexp, parse_defmacro, MacroEnv};
    use cranelisp::sexp::parse_sexp;

    let mut r = real_repl_session();
    let sexp = parse_sexp("(defmacro my-inc [x] (SexpList (slist (SexpSym \"+\") x (SexpInt 1))))")
        .unwrap();
    let info = parse_defmacro(&sexp).unwrap();
    let ptr = compile_macro(&mut r.tc, &mut r.jit, &info, Some(&r.macro_env)).unwrap();
    let mut env = MacroEnv::new();
    env.register(
        info.name,
        ptr,
        info.docstring,
        info.fixed_params,
        info.rest_param,
        Some(info.body_sexp),
    );

    // Expand (my-inc 41) → (+ 41 1)
    let call = parse_sexp("(my-inc 41)").unwrap();
    let expanded = expand_sexp(call, &env, 0).unwrap();
    let expanded_str = format!("{}", expanded);
    assert!(
        expanded_str.contains("+"),
        "expanded should contain +, got: {}",
        expanded_str
    );
    assert!(
        expanded_str.contains("41"),
        "expanded should contain 41, got: {}",
        expanded_str
    );
    assert!(
        expanded_str.contains("1"),
        "expanded should contain 1, got: {}",
        expanded_str
    );
}

// ── Quasiquote integration tests ────────────────────────────────────

#[test]
fn macro_quasiquote_simple_form() {
    // Macro using quasiquote to build (if ~c ~b 0)
    let src = r#"
        (defmacro when [c b]
          `(if ~c ~b 0))
        (defn main [] (pure (when true 42)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_quasiquote_false_branch() {
    let src = r#"
        (defmacro when [c b]
          `(if ~c ~b 0))
        (defn main [] (pure (when false 42)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 0);
}

#[test]
fn macro_quasiquote_bracket() {
    // Macro with bracket in quasiquote for let binding
    let src = r#"
        (defmacro my-let1 [v e b]
          `(let [~v ~e] ~b))
        (defn main [] (pure (my-let1 x 42 x)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_quasiquote_atom() {
    // Quasiquoted atom: macro that returns a literal int
    let src = r#"
        (defmacro q-int [] `42)
        (defn main [] (pure (q-int)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_quasiquote_splicing() {
    // Macro with ~@ splicing
    let src = r#"
        (defmacro my-add [& args]
          `(+ ~@args))
        (defn main [] (pure (my-add 40 2)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_quasiquote_inc() {
    // Same as manual sexp-building version, but using quasiquote
    let src = r#"
        (defmacro my-inc [x]
          `(+ ~x 1))
        (defn main [] (pure (my-inc 41)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

#[test]
fn macro_quasiquote_nested_usage() {
    // Quasiquote macro used in nested position
    let src = r#"
        (defmacro my-inc [x]
          `(+ ~x 1))
        (defn main [] (pure (* (my-inc 5) 7)))
    "#;
    assert_eq!(compile_and_run_with_macros(src).unwrap(), 42);
}

// ── Thread-first macro (->)  ────────────────────────────────────────────

#[test]
fn thread_first_single_value() {
    let src = r#"(defn main [] (pure (-> 42)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 42);
}

#[test]
fn thread_first_bare_symbol() {
    let src = r#"(defn main [] (pure (-> 5 inc)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 6);
}

#[test]
fn thread_first_multi_form() {
    // (-> 5 inc (* 2)) => (* (inc 5) 2) = 12
    let src = r#"(defn main [] (pure (-> 5 inc (* 2))))"#;
    assert_eq!(compile_and_run(src).unwrap(), 12);
}

#[test]
fn thread_first_nested() {
    // (-> 1 (+ 2) (* 3)) => (* (+ 1 2) 3) = 9
    let src = r#"(defn main [] (pure (-> 1 (+ 2) (* 3))))"#;
    assert_eq!(compile_and_run(src).unwrap(), 9);
}

// ── Thread-last macro (->>) ─────────────────────────────────────────────

#[test]
fn thread_last_single_value() {
    let src = r#"(defn main [] (pure (->> 42)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 42);
}

#[test]
fn thread_last_bare_symbol() {
    let src = r#"(defn main [] (pure (->> 5 inc)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 6);
}

#[test]
fn thread_last_multi_form() {
    // (->> 2 (* 3) (+ 10)) => (+ 10 (* 3 2)) = 16
    let src = r#"(defn main [] (pure (->> 2 (* 3) (+ 10))))"#;
    assert_eq!(compile_and_run(src).unwrap(), 16);
}

// ── Cond macro ──────────────────────────────────────────────────────────

#[test]
fn cond_first_match() {
    let src = r#"(defn main [] (pure (cond true 42 0)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 42);
}

#[test]
fn cond_second_match() {
    let src = r#"(defn main [] (pure (cond false 1 true 42 0)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 42);
}

#[test]
fn cond_default() {
    let src = r#"(defn main [] (pure (cond false 1 false 2 42)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 42);
}

#[test]
fn cond_with_comparison() {
    let src = r#"
        (defn classify [:Int x]
          (cond (< x 0) -1
                (= x 0) 0
                1))
        (defn main [] (pure (+ (+ (classify -5) (classify 0)) (classify 7))))
    "#;
    // -1 + 0 + 1 = 0
    assert_eq!(compile_and_run(src).unwrap(), 0);
}

// ── Case macro ──────────────────────────────────────────────────────────

#[test]
fn case_first_match() {
    let src = r#"(defn main [] (pure (case 1 1 10 2 20 0)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 10);
}

#[test]
fn case_second_match() {
    let src = r#"(defn main [] (pure (case 2 1 10 2 20 0)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 20);
}

#[test]
fn case_default() {
    let src = r#"(defn main [] (pure (case 99 1 10 2 20 0)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 0);
}

#[test]
fn case_with_expression() {
    let src = r#"
        (defn main [] (pure (case (+ 1 1) 1 10 2 20 0)))
    "#;
    assert_eq!(compile_and_run(src).unwrap(), 20);
}

// ── Vec macro ───────────────────────────────────────────────────────────

#[test]
fn vec_macro_elements() {
    let src = r#"(defn main [] (pure (vec-len (vec 1 2 3))))"#;
    assert_eq!(compile_and_run(src).unwrap(), 3);
}

#[test]
fn vec_macro_empty() {
    let src = r#"(defn main [] (pure (vec-len (vec))))"#;
    assert_eq!(compile_and_run(src).unwrap(), 0);
}

#[test]
fn vec_macro_access() {
    let src = r#"(defn main [] (pure (vec-get (vec 10 20 30) 1)))"#;
    assert_eq!(compile_and_run(src).unwrap(), 20);
}

// ── Sexp parser: -> and ->> as symbols ──────────────────────────────────

#[test]
fn sexp_thread_first_is_symbol() {
    use cranelisp::sexp::{parse_sexp, Sexp};
    let sexp = parse_sexp("->").unwrap();
    assert_eq!(sexp, Sexp::Symbol("->".to_string(), (0, 2)));
}

#[test]
fn sexp_thread_last_is_symbol() {
    use cranelisp::sexp::{parse_sexp, Sexp};
    let sexp = parse_sexp("->>").unwrap();
    assert_eq!(sexp, Sexp::Symbol("->>".to_string(), (0, 3)));
}

#[test]
fn sexp_minus_still_works() {
    use cranelisp::sexp::{parse_sexp, Sexp};
    let sexp = parse_sexp("(- 3 1)").unwrap();
    match sexp {
        Sexp::List(children, _) => {
            assert_eq!(children[0], Sexp::Symbol("-".to_string(), (1, 2)));
            assert_eq!(children[1], Sexp::Int(3, (3, 4)));
            assert_eq!(children[2], Sexp::Int(1, (5, 6)));
        }
        other => panic!("expected List, got {:?}", other),
    }
}

#[test]
fn sexp_negative_int_still_works() {
    use cranelisp::sexp::{parse_sexp, Sexp};
    let sexp = parse_sexp("-3").unwrap();
    assert_eq!(sexp, Sexp::Int(-3, (0, 2)));
}

// ── Example file tests ──────────────────────────────────────────────────
// These compile and run the actual example files via include_str!
// to ensure they stay in sync with the test suite.

#[test]
fn example_hello() {
    // Output: 42
    assert_eq!(
        compile_and_run(include_str!("../examples/hello.cl")).unwrap(),
        0
    );
}

#[test]
fn example_factorial() {
    // Output: 3628800
    assert_eq!(
        compile_and_run(include_str!("../examples/factorial.cl")).unwrap(),
        0
    );
}

#[test]
fn example_strings() {
    // Output: hello, world! / 42 / true
    assert_eq!(
        compile_and_run(include_str!("../examples/strings.cl")).unwrap(),
        0
    );
}

#[test]
fn example_closure() {
    // Output: 8, 13, 49
    assert_eq!(
        compile_and_run(include_str!("../examples/closure.cl")).unwrap(),
        0
    );
}

#[test]
fn example_float() {
    // Output: 4.0, 6.28
    assert_eq!(
        compile_and_run(include_str!("../examples/float.cl")).unwrap(),
        0
    );
}

#[test]
fn example_traits() {
    // Output: 42
    assert_eq!(
        compile_and_run(include_str!("../examples/traits.cl")).unwrap(),
        0
    );
}

#[test]
fn example_adt() {
    // Output: 3, 2, 42, 99, Red, 42, 3.14
    assert_eq!(
        compile_and_run(include_str!("../examples/adt.cl")).unwrap(),
        0
    );
}

#[test]
fn example_list() {
    // Output: true, false, 42, 2, 5
    assert_eq!(
        compile_and_run(include_str!("../examples/list.cl")).unwrap(),
        0
    );
}

#[test]
fn example_vec() {
    // Output: 5, 3, 6; returns 99
    assert_eq!(
        compile_and_run(include_str!("../examples/vec.cl")).unwrap(),
        99
    );
}

#[test]
fn example_seq() {
    // Output: 0, 11, 15, 32, 3, 42
    assert_eq!(
        compile_and_run(include_str!("../examples/seq.cl")).unwrap(),
        0
    );
}

#[test]
fn example_curry() {
    // Output: 3, 6, 15
    assert_eq!(
        compile_and_run(include_str!("../examples/curry.cl")).unwrap(),
        0
    );
}

#[test]
fn example_mapfold() {
    // Output: 9, 15, 6, 15, 55
    assert_eq!(
        compile_and_run(include_str!("../examples/mapfold.cl")).unwrap(),
        0
    );
}

#[test]
fn example_threading() {
    // Output: 12, 16, 1, 20, 3
    assert_eq!(
        compile_and_run(include_str!("../examples/threading.cl")).unwrap(),
        0
    );
}

#[test]
fn example_functor() {
    // Output: 6, false, 2, 4, 6
    assert_eq!(
        compile_and_run(include_str!("../examples/functor.cl")).unwrap(),
        0
    );
}

#[test]
fn example_macro() {
    // Output: 42, newline, 42, newline
    assert_eq!(
        compile_and_run(include_str!("../examples/macro.cl")).unwrap(),
        0
    );
}

#[test]
fn example_dot_notation() {
    // Output: Some(42), None, 3, 99, 5
    assert_eq!(
        compile_and_run(include_str!("../examples/dot_notation.cl")).unwrap(),
        0
    );
}

// ── Module system tests ─────────────────────────────────────────────────

#[test]
fn example_modules() {
    // Multi-file project: main.cl imports util.cl and math.cl
    // Output: 43, 42, 100
    let entry = std::path::Path::new("examples/modules/main.cl");
    cranelisp::batch::run_project(entry).unwrap();
}

#[test]
fn single_file_via_run_project() {
    // Single-file programs should work via run_project too
    let entry = std::path::Path::new("examples/hello.cl");
    cranelisp::batch::run_project(entry).unwrap();
}

#[test]
fn module_missing_file_error() {
    // (mod nonexistent) should produce a clear error
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let mut f = std::fs::File::create(&main_path).unwrap();
    writeln!(f, "(mod nonexistent)").unwrap();
    writeln!(f, "(defn main [] 0)").unwrap();
    drop(f);
    let result = cranelisp::batch::run_project(&main_path);
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("nonexistent"),
        "error should mention the missing module, got: {}",
        err_msg
    );
}

#[test]
fn module_cycle_detection() {
    // Circular dependency should be detected
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let a_path = dir.path().join("a.cl");
    let b_path = dir.path().join("b.cl");
    let mut fa = std::fs::File::create(&a_path).unwrap();
    writeln!(fa, "(mod b)").unwrap();
    writeln!(fa, "(defn main [] 0)").unwrap();
    drop(fa);
    let mut fb = std::fs::File::create(&b_path).unwrap();
    writeln!(fb, "(mod a)").unwrap();
    drop(fb);
    let result = cranelisp::batch::run_project(&a_path);
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("cycle") || err_msg.contains("circular"),
        "error should mention cycle, got: {}",
        err_msg
    );
}

#[test]
fn module_qualified_name_resolution() {
    // Qualified names from another module should resolve
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let helper_path = dir.path().join("helper.cl");
    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod helper)").unwrap();
    writeln!(fm, "(defn main [] (helper/inc-value 41))").unwrap();
    drop(fm);
    let mut fh = std::fs::File::create(&helper_path).unwrap();
    writeln!(fh, "(defn inc-value [:Int x] :Int (+ x 1))").unwrap();
    drop(fh);
    cranelisp::batch::run_project(&main_path).unwrap();
}

#[test]
fn module_unknown_qualified_name_error() {
    // Using a qualified name from an unknown module should error
    let src = r#"
        (defn main [] (nonexistent/foo 1))
    "#;
    let result = compile_and_run(src);
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("unknown module"),
        "expected unknown module error, got: {}",
        err_msg
    );
}

// ── Import tests ──────────────────────────────────────────────────────

#[test]
fn example_imports() {
    // Multi-file project with explicit imports
    let entry = std::path::Path::new("examples/imports/main.cl");
    cranelisp::batch::run_project(entry).unwrap();
}

#[test]
fn import_specific_names() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    writeln!(fm, "(import [util [helper]])").unwrap();
    writeln!(fm, "(defn main [] (pure (helper 41)))").unwrap();
    drop(fm);

    cranelisp::batch::run_project(&main_path).unwrap();
}

#[test]
fn import_glob() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    writeln!(fu, "(defn double [:Int x] :Int (* x 2))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    writeln!(fm, "(import [util [*]])").unwrap();
    writeln!(fm, "(defn main [] (pure (helper (double 20))))").unwrap();
    drop(fm);

    cranelisp::batch::run_project(&main_path).unwrap();
}

#[test]
fn import_nonexistent_name_errors() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int x)").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    writeln!(fm, "(import [util [nonexistent]])").unwrap();
    writeln!(fm, "(defn main [] (pure 0))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(result.is_err());
    let msg = format!("{}", result.unwrap_err());
    assert!(msg.contains("not a public name"), "got: {}", msg);
}

#[test]
fn import_undeclared_module_errors() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int x)").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    // Import from a module not declared with (mod ...)
    writeln!(fm, "(import [missing [foo]])").unwrap();
    writeln!(fm, "(defn main [] (pure 0))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(result.is_err());
    let msg = format!("{}", result.unwrap_err());
    assert!(msg.contains("not found"), "got: {}", msg);
}

#[test]
fn qualified_access_still_works_without_import() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    // No import — use qualified name
    writeln!(fm, "(defn main [] (pure (util/helper 99)))").unwrap();
    drop(fm);

    cranelisp::batch::run_project(&main_path).unwrap();
}

#[test]
fn bare_name_from_non_imported_module_not_accessible() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    // No import — bare name should not resolve
    writeln!(fm, "(defn main [] (pure (helper 99)))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(
        result.is_err(),
        "bare name from non-imported module should not resolve"
    );
}

// ── Visibility tests ──────────────────────────────────────────────────

#[test]
fn private_defn_not_accessible_via_qualified() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    writeln!(fu, "(defn- internal [:Int x] :Int (* x x))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    writeln!(fm, "(defn main [] (pure (util/internal 5)))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(
        result.is_err(),
        "private defn should not be accessible via qualified name"
    );
}

#[test]
fn private_defn_not_importable() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    writeln!(fu, "(defn- internal [:Int x] :Int (* x x))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    writeln!(fm, "(import [util [internal]])").unwrap();
    writeln!(fm, "(defn main [] (pure (internal 5)))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(result.is_err(), "private defn should not be importable");
    let msg = format!("{}", result.unwrap_err());
    assert!(msg.contains("not a public name"), "got: {}", msg);
}

#[test]
fn public_defn_accessible_via_qualified() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    writeln!(fu, "(defn- internal [:Int x] :Int (* x x))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    writeln!(fm, "(defn main [] (pure (util/helper 41)))").unwrap();
    drop(fm);

    cranelisp::batch::run_project(&main_path).unwrap();
}

#[test]
fn private_deftype_constructors_not_importable() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let types_path = dir.path().join("types.cl");

    let mut ft = std::fs::File::create(&types_path).unwrap();
    writeln!(ft, "(deftype- Secret [:Int val])").unwrap();
    drop(ft);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod types)").unwrap();
    writeln!(fm, "(import [types [Secret]])").unwrap();
    writeln!(fm, "(defn main [] (pure 0))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(result.is_err(), "private type should not be importable");
    let msg = format!("{}", result.unwrap_err());
    assert!(msg.contains("not a public name"), "got: {}", msg);
}

#[test]
fn glob_import_skips_private() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    writeln!(fu, "(defn- internal [:Int x] :Int (* x x))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    writeln!(fm, "(import [util [*]])").unwrap();
    // helper should be available, internal should not
    writeln!(fm, "(defn main [] (pure (helper 41)))").unwrap();
    drop(fm);

    cranelisp::batch::run_project(&main_path).unwrap();
}

// ── Export tests ──────────────────────────────────────────────────────

#[test]
fn export_re_exports_names() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let facade_path = dir.path().join("facade.cl");
    let impl_path = dir.path().join("impl.cl");

    // impl module defines the actual function
    let mut fi = std::fs::File::create(&impl_path).unwrap();
    writeln!(fi, "(defn helper [:Int x] :Int (+ x 10))").unwrap();
    drop(fi);

    // facade re-exports helper from impl
    let mut ff = std::fs::File::create(&facade_path).unwrap();
    writeln!(ff, "(mod impl)").unwrap();
    writeln!(ff, "(import [impl [helper]])").unwrap();
    writeln!(ff, "(export [impl [helper]])").unwrap();
    drop(ff);

    // main imports from facade
    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod facade)").unwrap();
    writeln!(fm, "(import [facade [helper]])").unwrap();
    writeln!(fm, "(defn main [] (pure (helper 32)))").unwrap();
    drop(fm);

    cranelisp::batch::run_project(&main_path).unwrap();
}

#[test]
fn export_cannot_reexport_private() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let facade_path = dir.path().join("facade.cl");
    let impl_path = dir.path().join("impl.cl");

    let mut fi = std::fs::File::create(&impl_path).unwrap();
    writeln!(fi, "(defn- internal [:Int x] :Int x)").unwrap();
    drop(fi);

    let mut ff = std::fs::File::create(&facade_path).unwrap();
    writeln!(ff, "(mod impl)").unwrap();
    writeln!(ff, "(export [impl [internal]])").unwrap();
    drop(ff);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod facade)").unwrap();
    writeln!(fm, "(defn main [] (pure 0))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(result.is_err(), "cannot re-export private names");
    let msg = format!("{}", result.unwrap_err());
    assert!(msg.contains("not a public name"), "got: {}", msg);
}

// ── Ambiguity checking tests ──────────────────────────────────────────

#[test]
fn ambiguous_import_same_name_different_sources() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let a_path = dir.path().join("a.cl");
    let b_path = dir.path().join("b.cl");

    let mut fa = std::fs::File::create(&a_path).unwrap();
    writeln!(fa, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    drop(fa);

    let mut fb = std::fs::File::create(&b_path).unwrap();
    writeln!(fb, "(defn helper [:Int x] :Int (* x 2))").unwrap();
    drop(fb);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod a)").unwrap();
    writeln!(fm, "(mod b)").unwrap();
    writeln!(fm, "(import [a [helper] b [helper]])").unwrap();
    writeln!(fm, "(defn main [] (pure (helper 5)))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(result.is_err(), "ambiguous import should error when used");
    let msg = format!("{}", result.unwrap_err());
    assert!(
        msg.contains("ambiguous bare name"),
        "expected 'ambiguous bare name' error, got: {}",
        msg
    );
}

#[test]
fn definition_conflicts_with_import() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    writeln!(fm, "(import [util [helper]])").unwrap();
    // Defining helper when it's already imported should conflict
    writeln!(fm, "(defn helper [:Int x] :Int (* x 2))").unwrap();
    writeln!(fm, "(defn main [] (pure (helper 5)))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(
        result.is_err(),
        "definition conflicting with import should error"
    );
    let msg = format!("{}", result.unwrap_err());
    assert!(msg.contains("conflicts with import"), "got: {}", msg);
}

#[test]
fn import_shadows_prelude_allowed() {
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let util_path = dir.path().join("util.cl");

    // Define a function with a prelude name (e.g., "show" would be tricky since it's a trait method)
    // Instead test that importing a name that happens to shadow prelude works fine
    let mut fu = std::fs::File::create(&util_path).unwrap();
    writeln!(fu, "(defn my-fn [:Int x] :Int (+ x 100))").unwrap();
    drop(fu);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod util)").unwrap();
    writeln!(fm, "(import [util [my-fn]])").unwrap();
    writeln!(fm, "(defn main [] (pure (my-fn 1)))").unwrap();
    drop(fm);

    // Should succeed — import takes precedence over prelude
    cranelisp::batch::run_project(&main_path).unwrap();
}

// ===== Module visibility: synthetic modules & qualified names =====

#[test]
fn init_builtins_registers_qualified_only() {
    // After init_builtins, primitives should only be available as qualified names,
    // not as bare names in universal.
    let mut tc = TypeChecker::new();
    tc.init_builtins();
    // Bare name should NOT be accessible
    assert!(
        tc.lookup("add-i64").is_none(),
        "add-i64 should not be bare-accessible after init_builtins"
    );
    // Qualified name SHOULD be accessible
    assert!(
        tc.lookup("primitives/add-i64").is_some(),
        "primitives/add-i64 should be accessible"
    );
}

#[test]
fn init_builtins_no_platform_module() {
    // After removing built-in platform, init_builtins should NOT create platform.stdio
    let mut tc = TypeChecker::new();
    tc.init_builtins();
    assert!(
        tc.lookup("platform.stdio/print").is_none(),
        "platform.stdio/print should not exist without loading a platform DLL"
    );
}

#[test]
fn get_module_public_names_primitives() {
    let mut tc = TypeChecker::new();
    tc.init_builtins();
    let names = tc.get_module_public_names("primitives");
    assert!(
        names.contains(&"add-i64".to_string()),
        "primitives module should contain add-i64"
    );
    assert!(
        !names.contains(&"print".to_string()),
        "primitives module should not contain print"
    );
}

#[test]
fn get_module_public_names_platform_empty_without_dll() {
    // Without loading a platform DLL, platform.stdio should not exist
    let mut tc = TypeChecker::new();
    tc.init_builtins();
    let names = tc.get_module_public_names("platform.stdio");
    assert!(
        names.is_empty(),
        "platform.stdio should have no names without loading a DLL"
    );
}

#[test]
fn repl_full_session_primitives_not_in_user_scope() {
    // Inline primitives like add-f64 should not be visible in user scope
    // Uses the full REPL session with module-based prelude loading.
    let mut r = cranelisp::repl::ReplSession::new().unwrap();
    r.load_prelude();
    assert!(
        r.tc.describe_symbol("add-f64").is_none(),
        "add-f64 should not be visible in user scope"
    );
    assert!(
        r.tc.describe_symbol("eq-i64").is_none(),
        "eq-i64 should not be visible in user scope"
    );
}

#[test]
fn repl_full_session_qualified_primitive_accessible() {
    // Qualified access to primitives should work
    let mut r = cranelisp::repl::ReplSession::new().unwrap();
    r.load_prelude();
    match r.tc.describe_symbol("primitives/add-f64") {
        Some(SymbolInfo::InlinePrimitive { .. }) => {}
        other => panic!(
            "expected InlinePrimitive for primitives/add-f64, got {:?}",
            other.map(|_| "some other variant")
        ),
    }
}

#[test]
fn repl_full_session_print_not_visible_without_platform() {
    // Without loading a platform, print should NOT be visible
    let mut r = cranelisp::repl::ReplSession::new().unwrap();
    r.load_prelude();
    assert!(
        r.tc.describe_symbol("print").is_none(),
        "print should not be visible without loading a platform"
    );
}

#[test]
fn repl_full_session_qualified_name_primitives() {
    // Qualified access to a prelude-exported symbol should work
    let mut r = cranelisp::repl::ReplSession::new().unwrap();
    r.load_prelude();
    let qualified = r.tc.qualified_name("inc");
    assert!(
        !qualified.module.is_root(),
        "inc should have a qualified form, got: {}",
        qualified
    );
}

#[test]
fn repl_full_session_fold_helpers_not_visible() {
    // Private fold helpers (defn-) should not be visible in user scope
    let mut r = cranelisp::repl::ReplSession::new().unwrap();
    r.load_prelude();
    assert!(
        r.tc.describe_symbol("bind!-fold").is_none(),
        "bind!-fold should not be visible (it's defn- in core)"
    );
    assert!(
        r.tc.describe_symbol("thread-first-fold").is_none(),
        "thread-first-fold should not be visible"
    );
    assert!(
        r.tc.describe_symbol("cond-fold").is_none(),
        "cond-fold should not be visible"
    );
}

#[test]
fn repl_full_session_list_no_inline_primitives() {
    // /l listing should not include inline primitives like add-i64
    let mut r = cranelisp::repl::ReplSession::new().unwrap();
    r.load_prelude();
    let symbols = r.tc.list_symbols();
    for (name, info) in &symbols {
        if let SymbolInfo::InlinePrimitive { .. } = info {
            panic!("unexpected inline primitive in list_symbols: {}", name);
        }
    }
}

#[test]
fn repl_full_session_overloaded_fn_qualified() {
    // Overloaded functions like map should have a qualified name
    let mut r = cranelisp::repl::ReplSession::new().unwrap();
    r.load_prelude();
    let qualified = r.tc.qualified_name("map");
    assert!(
        !qualified.module.is_root(),
        "map should have a qualified form, got: {}",
        qualified
    );
}

#[test]
fn repl_full_session_get_module_public_names_excludes_private() {
    // defn- items should not appear in module public names
    let mut r = cranelisp::repl::ReplSession::new().unwrap();
    r.load_prelude();
    let core_names = r.tc.get_module_public_names("core");
    assert!(
        !core_names.contains(&"bind!-fold".to_string()),
        "bind!-fold (defn-) should not be in core's public names"
    );
    assert!(
        !core_names.contains(&"thread-first-fold".to_string()),
        "thread-first-fold (defn-) should not be in core's public names"
    );
}

// ── KNOWN ISSUE tests ──────────────────────────────────────────────────
//
// The ignored tests below are expected failures for known issues.
// They are excluded from the normal test suite because they terminate
// the process (via hardware traps or process::exit), which kills the
// test runner rather than producing a catchable panic.
// Run manually with: cargo test -- --ignored

#[test]
#[ignore] // KNOWN ISSUE: expected failure — traps the process via Cranelift sdiv (not a Rust panic)
fn known_issue_division_by_zero_traps() {
    let src = r#"(defn main [] (pure (/ 1 0)))"#;
    let _ = compile_and_run(src);
}

#[test]
#[ignore] // KNOWN ISSUE: expected failure — calls process::exit(1) on missing match arm
fn known_issue_non_exhaustive_match_panics() {
    let src = r#"
        (deftype Color Red Green Blue)
        (defn main []
          (pure (match Red [Green 1 Blue 2])))
    "#;
    let _ = compile_and_run(src);
}

#[test]
#[ignore] // KNOWN ISSUE: expected failure — calls process::exit(1) on out-of-bounds index
fn known_issue_vec_out_of_bounds() {
    let src = r#"(defn main [] (pure (vec-get [1 2 3] 10)))"#;
    let _ = compile_and_run(src);
}

#[test]
fn known_issue_integer_overflow_wraps() {
    // KNOWN ISSUE: iadd wraps silently (64-bit two's complement)
    let src = r#"(defn main [] (pure (+ 9223372036854775807 1)))"#;
    let result = compile_and_run(src).unwrap();
    assert!(result < 0, "expected negative wrap-around, got {}", result);
}

#[test]
fn known_issue_adt_accessor_shadowing() {
    // KNOWN ISSUE: accessor functions are global; two types with the same
    // field name conflict. The first definition's type wins in the env,
    // so the second type's accessor produces a type error.
    let mut r = ReplSession::new();
    r.typedef("(deftype Foo [:Int label])").unwrap();
    r.typedef("(deftype Bar [:Int label])").unwrap();
    // `label` retains the type Foo -> Int; calling it on Foo works
    let foo_label = r.eval("(label (Foo 42))").unwrap();
    assert_eq!(foo_label, 42);
    // Calling `label` on Bar produces a type error
    let bar_result = r.eval("(label (Bar 99))");
    assert!(
        bar_result.is_err(),
        "expected type error from accessor name collision"
    );
}

#[test]
fn known_issue_qualified_name_resolution_error() {
    // KNOWN ISSUE: qualified names parse but do not resolve
    let result = compile_and_run(r#"(defn main [] (pure core.option/Some))"#);
    assert!(result.is_err(), "expected error for qualified name, got Ok");
}

// ── Ambiguity handling tests ─────────────────────────────────────────

#[test]
fn ambiguous_trait_method_bare_name_errors() {
    // Two traits with the same method name → bare name is ambiguous
    let src = r#"
        (deftrait Debug (show [self] String))
        (impl Debug Int (defn show [x] "debug"))
        (defn main [] (print (show 42)))
    "#;
    let result = compile_and_run(src);
    assert!(result.is_err(), "bare 'show' should be ambiguous");
    let msg = format!("{}", result.unwrap_err());
    assert!(
        msg.contains("ambiguous bare name 'show'"),
        "expected ambiguous bare name error, got: {}",
        msg
    );
}

#[test]
#[ignore] // KNOWN ISSUE: method resolution doesn't track which trait a dotted call belongs to
fn ambiguous_trait_method_dotted_name_works() {
    // Even when bare 'show' is ambiguous, 'Display.show' should resolve directly.
    // Debug impl uses a custom type to avoid mangled name collision with Display.show$Int.
    // Currently fails because resolve_methods doesn't know Display.show should dispatch via Display.
    let src = r#"
        (deftype Wrapper (MkW [:Int val]))
        (deftrait Debug (show [self] String))
        (impl Debug Wrapper (defn show [w] "debug"))
        (defn main [] (print (Display.show 42)))
    "#;
    let result = compile_and_run(src);
    assert!(result.is_ok(), "Display.show should bypass ambiguity: {:?}", result);
}

#[test]
fn ambiguous_import_qualified_bypass() {
    // Import collision: both modules export 'helper'. Qualified access works.
    use std::io::Write;
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.cl");
    let a_path = dir.path().join("a.cl");
    let b_path = dir.path().join("b.cl");

    let mut fa = std::fs::File::create(&a_path).unwrap();
    writeln!(fa, "(defn helper [:Int x] :Int (+ x 1))").unwrap();
    drop(fa);

    let mut fb = std::fs::File::create(&b_path).unwrap();
    writeln!(fb, "(defn helper [:Int x] :Int (* x 2))").unwrap();
    drop(fb);

    let mut fm = std::fs::File::create(&main_path).unwrap();
    writeln!(fm, "(mod a)").unwrap();
    writeln!(fm, "(mod b)").unwrap();
    writeln!(fm, "(import [a [helper] b [helper]])").unwrap();
    writeln!(fm, "(defn main [] (pure (a/helper 5)))").unwrap();
    drop(fm);

    let result = cranelisp::batch::run_project(&main_path);
    assert!(result.is_ok(), "qualified a/helper should bypass ambiguity: {:?}", result);
}

#[test]
fn repl_ambiguous_trait_method_describe() {
    let mut r = ReplSession::new();
    // ReplSession::new() already loaded Display trait with 'show'.
    // Define a second trait with the same method name.
    let src = "(deftrait Debug (show [self] String))";
    let items = parse_program(src).unwrap();
    for item in &items {
        if let cranelisp::ast::TopLevel::TraitDecl(td) = item {
            for method in &td.methods {
                r.jit.register_trait_method(&method.name);
            }
            r.tc.register_trait_public(td);
        }
    }
    // /info show should report ambiguity
    let info = r.tc.describe_symbol("show");
    match info {
        Some(cranelisp::typechecker::SymbolInfo::Ambiguous { alternatives }) => {
            assert!(
                alternatives.iter().any(|a| a.contains("Display")),
                "should list Display.show: {:?}",
                alternatives
            );
            assert!(
                alternatives.iter().any(|a| a.contains("Debug")),
                "should list Debug.show: {:?}",
                alternatives
            );
        }
        _ => panic!("expected Ambiguous symbol info for 'show'"),
    }
}

#[test]
#[ignore] // KNOWN ISSUE: runtime panic calls process::exit(1), killing the test process in parallel mode
fn dotted_field_accessor_resolution() {
    // Type.field syntax resolves field accessors
    let src = r#"
        (deftype (Wrapper a) (Wrap [:a val]))
        (deftype (Box a) (MkBox [:a val]))
        (defn main [] (pure (Wrapper.val (Wrap 42))))
    "#;
    let result = compile_and_run(src);
    assert!(result.is_ok(), "Wrapper.val should resolve: {:?}", result);
    assert_eq!(result.unwrap(), 42);
}

// ── Full-prelude batch tests (const, def, begin, bare-symbol) ────────

/// Run a cranelisp program through the batch pipeline with the full prelude.
/// Creates a temp file in a directory where lib/ is discoverable.
fn run_batch(src: &str) -> std::process::Output {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("test.cl");
    std::fs::write(&file, src).unwrap();
    // Symlink lib dir so prelude is discoverable
    let lib_src = Path::new(env!("CARGO_MANIFEST_DIR")).join("lib");
    std::os::unix::fs::symlink(&lib_src, dir.path().join("lib")).unwrap();
    // Symlink target/debug so platform DLLs are discoverable
    let target_debug = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/debug");
    if target_debug.exists() {
        std::fs::create_dir_all(dir.path().join("target")).unwrap();
        std::os::unix::fs::symlink(&target_debug, dir.path().join("target/debug")).unwrap();
    }
    std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
        .args(["--run", file.to_str().unwrap()])
        .output()
        .unwrap()
}

#[test]
fn batch_const_int() {
    let output = run_batch("(platform stdio)\n(import [platform.stdio [*]])\n(const ANSWER 42) (defn main [] (print (show ANSWER)))");
    assert!(output.status.success(), "const int failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}

#[test]
fn batch_const_float() {
    let output = run_batch("(platform stdio)\n(import [platform.stdio [*]])\n(const PI 3.14) (defn main [] (print (show PI)))");
    assert!(output.status.success(), "const float failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "3.14");
}

#[test]
fn batch_const_string() {
    let output = run_batch("(platform stdio)\n(import [platform.stdio [*]])\n(const GREETING \"hello\") (defn main [] (print GREETING))");
    assert!(output.status.success(), "const string failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "hello");
}

#[test]
fn batch_def_basic() {
    let output = run_batch("(platform stdio)\n(import [platform.stdio [*]])\n(def answer 42) (defn main [] (print (show answer)))");
    assert!(output.status.success(), "def basic failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}

#[test]
fn batch_def_expression() {
    let output = run_batch("(platform stdio)\n(import [platform.stdio [*]])\n(def ten (+ 5 5)) (defn main [] (print (show ten)))");
    assert!(output.status.success(), "def expression failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "10");
}

#[test]
fn batch_def_got_call() {
    // def creates a zero-arg function via GOT — verify it evaluates correctly
    let output = run_batch("(platform stdio)\n(import [platform.stdio [*]])\n(def pi 3.14) (defn main [] (print (show pi)))");
    assert!(output.status.success(), "def GOT call failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "3.14");
}

#[test]
fn batch_defmacro_bad_return_type() {
    let output = run_batch(r#"(defmacro bad [] 3.14) (defn main [] (pure 0))"#);
    assert!(!output.status.success(), "should fail with type error");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("expected Sexp"), "should mention Sexp in error: {}", stderr);
}

#[test]
fn batch_bare_symbol_expansion() {
    // Zero-arg macro expands when used as bare symbol (no parens)
    let output = run_batch(r#"
        (defmacro always-one [] (SexpInt 1))
        (defn main [] (pure always-one))
    "#);
    assert!(output.status.success(), "bare symbol expansion failed: {}", String::from_utf8_lossy(&output.stderr));
}

#[test]
fn batch_begin_expansion() {
    // A macro that expands to (begin ...) should have both forms processed
    let output = run_batch(r#"
        (platform stdio)
        (import [platform.stdio [*]])
        (def answer 42)
        (defn main [] (print (show answer)))
    "#);
    assert!(output.status.success(), "begin expansion failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}

#[test]
fn batch_str_concat() {
    let output = run_batch("(platform stdio)\n(import [platform.stdio [*]])\n(defn main [] (print (str-concat \"hello\" \" world\")))");
    assert!(output.status.success(), "str-concat failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "hello world");
}

#[test]
fn batch_str_macro_mixed_types() {
    let output = run_batch("(platform stdio)\n(import [platform.stdio [*]])\n(defn main [] (print (str \"val=\" 42 \" pi=\" 3.14 \" ok=\" true)))");
    assert!(output.status.success(), "str macro failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "val=42 pi=3.14 ok=true");
}

#[test]
fn batch_str_macro_empty() {
    let output = run_batch("(platform stdio)\n(import [platform.stdio [*]])\n(defn main [] (print (str)))");
    assert!(output.status.success(), "str macro empty failed: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "");
}

// ── Platform declaration tests ──────────────────────────────────────────

#[test]
fn batch_platform_nonexistent_error() {
    // (platform nonexistent) should produce a clear error
    let output = run_batch(r#"
        (platform nonexistent)
        (defn main [] (pure 0))
    "#);
    assert!(!output.status.success(), "expected failure for nonexistent platform");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("platform 'nonexistent' not found"), "error should mention platform not found: {}", stderr);
}

#[test]
fn batch_platform_missing_argument_error() {
    // (platform) with no argument should produce a parse error
    let output = run_batch(r#"
        (platform)
        (defn main [] (pure 0))
    "#);
    assert!(!output.status.success(), "expected failure for missing platform argument");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("(platform name)"), "error should mention platform syntax: {}", stderr);
}

// ── Cache tests ─────────────────────────────────────────────────────────

/// Create isolated test dir with COPIED lib/ (not symlinked) for cache isolation.
/// This prevents cache writes from polluting the real lib/.cranelisp-cache/.
fn setup_cache_test_dir() -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    let lib_src = Path::new(env!("CARGO_MANIFEST_DIR")).join("lib");
    let lib_dst = dir.path().join("lib");
    std::fs::create_dir_all(&lib_dst).unwrap();
    for entry in std::fs::read_dir(&lib_src).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map(|e| e == "cl").unwrap_or(false) {
            std::fs::copy(&path, lib_dst.join(entry.file_name())).unwrap();
        } else if path.is_dir() && entry.file_name() != ".cranelisp-cache" {
            // Copy subdirectories (e.g. core/) recursively
            let sub_dst = lib_dst.join(entry.file_name());
            std::fs::create_dir_all(&sub_dst).unwrap();
            for sub_entry in std::fs::read_dir(&path).unwrap() {
                let sub_entry = sub_entry.unwrap();
                if sub_entry.path().extension().map(|e| e == "cl").unwrap_or(false) {
                    std::fs::copy(sub_entry.path(), sub_dst.join(sub_entry.file_name())).unwrap();
                }
            }
        }
    }
    // Symlink target/debug so platform DLLs are discoverable
    let target_debug = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/debug");
    if target_debug.exists() {
        std::fs::create_dir_all(dir.path().join("target")).unwrap();
        std::os::unix::fs::symlink(&target_debug, dir.path().join("target/debug")).unwrap();
    }
    dir
}

fn write_source(dir: &Path, filename: &str, src: &str) {
    std::fs::write(dir.join(filename), src).unwrap();
}

fn run_in_dir(dir: &Path, filename: &str) -> std::process::Output {
    std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
        .args(["--run", dir.join(filename).to_str().unwrap()])
        .output()
        .unwrap()
}

// ── Cache write & structure ─────────────────────────────────────────────

#[test]
fn cache_write_creates_files() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl", "(defn main [] (pure 0))");
    let output = run_in_dir(dir.path(), "test.cl");
    assert!(output.status.success(), "first run failed: {}", String::from_utf8_lossy(&output.stderr));

    // Project cache should exist
    let project_cache = dir.path().join(".cranelisp-cache");
    assert!(project_cache.exists(), "project .cranelisp-cache/ should exist");
    assert!(project_cache.join("manifest.json").exists(), "project manifest.json should exist");
    assert!(project_cache.join("test.meta.json").exists(), "test.meta.json should exist");

    // Lib cache should exist with core and submodule files
    let lib_cache = dir.path().join("lib/.cranelisp-cache");
    assert!(lib_cache.exists(), "lib .cranelisp-cache/ should exist");
    assert!(lib_cache.join("manifest.json").exists(), "lib manifest.json should exist");
    assert!(lib_cache.join("core.meta.json").exists(), "core.meta.json should exist");
    // core.cl is a thin re-export shell (no compiled code), so core.o doesn't exist;
    // submodule .o files exist instead
    assert!(lib_cache.join("numerics.o").exists(), "numerics.o should exist");
    assert!(lib_cache.join("collections.o").exists(), "collections.o should exist");
}

#[test]
fn cache_two_tier_separation() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl", "(defn main [] (pure 0))");
    let output = run_in_dir(dir.path(), "test.cl");
    assert!(output.status.success(), "run failed: {}", String::from_utf8_lossy(&output.stderr));

    let project_cache = dir.path().join(".cranelisp-cache");
    let lib_cache = dir.path().join("lib/.cranelisp-cache");

    // Lib modules should be in lib cache ONLY
    assert!(lib_cache.join("core.meta.json").exists(), "core should be in lib cache");
    assert!(lib_cache.join("prelude.meta.json").exists(), "prelude should be in lib cache");
    assert!(!project_cache.join("core.meta.json").exists(), "core should NOT be in project cache");
    assert!(!project_cache.join("prelude.meta.json").exists(), "prelude should NOT be in project cache");

    // Project module should be in project cache ONLY
    assert!(project_cache.join("test.meta.json").exists(), "test should be in project cache");
    assert!(!lib_cache.join("test.meta.json").exists(), "test should NOT be in lib cache");

    // Verify manifest contents
    let project_manifest: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(project_cache.join("manifest.json")).unwrap()).unwrap();
    let lib_manifest: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(lib_cache.join("manifest.json")).unwrap()).unwrap();

    let project_modules: Vec<String> = project_manifest["modules"].as_array().unwrap()
        .iter().map(|m| m["module_path"].as_str().unwrap().to_string()).collect();
    let lib_modules: Vec<String> = lib_manifest["modules"].as_array().unwrap()
        .iter().map(|m| m["module_path"].as_str().unwrap().to_string()).collect();

    assert!(project_modules.contains(&"test".to_string()), "project manifest should list test");
    assert!(!project_modules.contains(&"core".to_string()), "project manifest should NOT list core");
    assert!(lib_modules.contains(&"core".to_string()), "lib manifest should list core");
    assert!(lib_modules.contains(&"prelude".to_string()), "lib manifest should list prelude");
}

// ── Cache hit correctness ───────────────────────────────────────────────

#[test]
fn cache_hit_produces_same_output() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl",
        "(platform stdio)\n(import [platform.stdio [*]])\n(defn double [x] (* x 2))\n(defn main [] (print (show (double 21))))");

    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));
    let stdout1 = String::from_utf8_lossy(&output1.stdout).to_string();

    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "second run (cache hit) failed: {}", String::from_utf8_lossy(&output2.stderr));
    let stdout2 = String::from_utf8_lossy(&output2.stdout).to_string();

    assert_eq!(stdout1.trim(), "42");
    assert_eq!(stdout2.trim(), "42", "cache hit should produce same output");
}

#[test]
fn cache_hit_with_macros() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl", r#"
        (platform stdio)
        (import [platform.stdio [*]])
        (const ANSWER 42)
        (def greeting "hello")
        (defn main [] (print (str greeting " " ANSWER)))
    "#);

    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));

    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "second run (cache hit with macros) failed: {}", String::from_utf8_lossy(&output2.stderr));

    assert_eq!(String::from_utf8_lossy(&output1.stdout).trim(), "hello 42");
    assert_eq!(String::from_utf8_lossy(&output2.stdout).trim(), "hello 42");
}

#[test]
fn cache_adt_and_traits_from_cache() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl", r#"
        (platform stdio)
        (import [platform.stdio [*]])
        (deftype Color Red Green Blue)
        (defn color-name [c]
            (match c
                [Red "red"
                 Green "green"
                 Blue "blue"]))
        (defn main [] (print (color-name Green)))
    "#);

    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));

    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "second run (ADT from cache) failed: {}", String::from_utf8_lossy(&output2.stderr));

    assert_eq!(String::from_utf8_lossy(&output1.stdout).trim(), "green");
    assert_eq!(String::from_utf8_lossy(&output2.stdout).trim(), "green");
}

// ── Source invalidation ─────────────────────────────────────────────────

#[test]
fn cache_source_invalidation() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl",
        "(platform stdio)\n(import [platform.stdio [*]])\n(defn main [] (print \"version1\"))");

    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));
    assert_eq!(String::from_utf8_lossy(&output1.stdout).trim(), "version1");

    // Read the source hash from manifest
    let project_cache = dir.path().join(".cranelisp-cache");
    let manifest1: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(project_cache.join("manifest.json")).unwrap()).unwrap();
    let hash1 = manifest1["modules"].as_array().unwrap()
        .iter().find(|m| m["module_path"].as_str() == Some("test"))
        .unwrap()["source_hash"].as_str().unwrap().to_string();

    // Modify source
    write_source(dir.path(), "test.cl",
        "(platform stdio)\n(import [platform.stdio [*]])\n(defn main [] (print \"version2\"))");

    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "second run (invalidated) failed: {}", String::from_utf8_lossy(&output2.stderr));
    assert_eq!(String::from_utf8_lossy(&output2.stdout).trim(), "version2");

    // Source hash should have changed
    let manifest2: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(project_cache.join("manifest.json")).unwrap()).unwrap();
    let hash2 = manifest2["modules"].as_array().unwrap()
        .iter().find(|m| m["module_path"].as_str() == Some("test"))
        .unwrap()["source_hash"].as_str().unwrap().to_string();

    assert_ne!(hash1, hash2, "source hash should change after modification");
}

#[test]
fn cache_multimodule_partial_invalidation() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "helper.cl",
        "(defn double [:Int x] :Int (* x 2))");
    write_source(dir.path(), "test.cl", r#"
        (platform stdio)
        (import [platform.stdio [*]])
        (mod helper)
        (import [helper [double]])
        (defn main [] (print (show (double 21))))
    "#);

    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));
    assert_eq!(String::from_utf8_lossy(&output1.stdout).trim(), "42");

    // Record helper hash before modification
    let project_cache = dir.path().join(".cranelisp-cache");
    let manifest1: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(project_cache.join("manifest.json")).unwrap()).unwrap();
    let helper_hash1 = manifest1["modules"].as_array().unwrap()
        .iter().find(|m| m["module_path"].as_str() == Some("helper"))
        .unwrap()["source_hash"].as_str().unwrap().to_string();
    let test_hash1 = manifest1["modules"].as_array().unwrap()
        .iter().find(|m| m["module_path"].as_str() == Some("test"))
        .unwrap()["source_hash"].as_str().unwrap().to_string();

    // Modify ONLY helper
    write_source(dir.path(), "helper.cl",
        "(defn double [:Int x] :Int (* x 3))");

    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "second run failed: {}", String::from_utf8_lossy(&output2.stderr));
    assert_eq!(String::from_utf8_lossy(&output2.stdout).trim(), "63");

    let manifest2: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(project_cache.join("manifest.json")).unwrap()).unwrap();
    let helper_hash2 = manifest2["modules"].as_array().unwrap()
        .iter().find(|m| m["module_path"].as_str() == Some("helper"))
        .unwrap()["source_hash"].as_str().unwrap().to_string();
    let test_hash2 = manifest2["modules"].as_array().unwrap()
        .iter().find(|m| m["module_path"].as_str() == Some("test"))
        .unwrap()["source_hash"].as_str().unwrap().to_string();

    assert_ne!(helper_hash1, helper_hash2, "helper hash should change");
    assert_eq!(test_hash1, test_hash2, "test hash should stay the same (source unchanged)");
}

// ── Error recovery ──────────────────────────────────────────────────────

#[test]
fn cache_corrupted_meta_recovery() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl",
        "(platform stdio)\n(import [platform.stdio [*]])\n(defn main [] (print \"ok\"))");

    // First run to populate cache
    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));

    // Corrupt the lib cache core.meta.json with invalid JSON
    let lib_cache = dir.path().join("lib/.cranelisp-cache");
    std::fs::write(lib_cache.join("core.meta.json"), "{{INVALID JSON}}").unwrap();

    // Second run should recover by recompiling
    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "should recover from corrupted meta: {}", String::from_utf8_lossy(&output2.stderr));
    assert_eq!(String::from_utf8_lossy(&output2.stdout).trim(), "ok");
}

#[test]
fn cache_missing_meta_file_recovery() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl",
        "(platform stdio)\n(import [platform.stdio [*]])\n(defn main [] (print \"ok\"))");

    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));

    // Delete core.meta.json (and core.o) — manifest still says cache hit,
    // but try_load_cached_module returns None → falls through to recompilation
    let lib_cache = dir.path().join("lib/.cranelisp-cache");
    let _ = std::fs::remove_file(lib_cache.join("core.meta.json"));
    let _ = std::fs::remove_file(lib_cache.join("core.o"));

    // Should fall through to normal compilation
    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "should recover from missing meta: {}", String::from_utf8_lossy(&output2.stderr));
    assert_eq!(String::from_utf8_lossy(&output2.stdout).trim(), "ok");
}

#[test]
fn cache_deleted_cache_dir_recovery() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl",
        "(platform stdio)\n(import [platform.stdio [*]])\n(defn main [] (print \"ok\"))");

    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));

    // Delete both cache directories entirely
    let project_cache = dir.path().join(".cranelisp-cache");
    let lib_cache = dir.path().join("lib/.cranelisp-cache");
    if project_cache.exists() {
        std::fs::remove_dir_all(&project_cache).unwrap();
    }
    if lib_cache.exists() {
        std::fs::remove_dir_all(&lib_cache).unwrap();
    }

    // Should rebuild from scratch
    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "should rebuild after cache deletion: {}", String::from_utf8_lossy(&output2.stderr));
    assert_eq!(String::from_utf8_lossy(&output2.stdout).trim(), "ok");

    // Cache should be recreated
    assert!(project_cache.exists(), "project cache should be recreated");
    assert!(lib_cache.exists(), "lib cache should be recreated");
}

#[test]
fn cache_manifest_version_mismatch() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl",
        "(platform stdio)\n(import [platform.stdio [*]])\n(defn main [] (print \"ok\"))");

    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));

    // Tamper with lib manifest version
    let lib_cache = dir.path().join("lib/.cranelisp-cache");
    let manifest_path = lib_cache.join("manifest.json");
    let mut manifest: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&manifest_path).unwrap()).unwrap();
    manifest["cranelisp_version"] = serde_json::json!("99.99.99");
    std::fs::write(&manifest_path, serde_json::to_string_pretty(&manifest).unwrap()).unwrap();

    // Should ignore stale cache and recompile from source
    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "should recompile with version mismatch: {}", String::from_utf8_lossy(&output2.stderr));
    assert_eq!(String::from_utf8_lossy(&output2.stdout).trim(), "ok");
}

// ── Multi-module cache ──────────────────────────────────────────────────

#[test]
fn cache_multimodule_project() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "helper.cl",
        "(defn greet [:String name] :String (str-concat \"hello \" name))");
    write_source(dir.path(), "test.cl", r#"
        (platform stdio)
        (import [platform.stdio [*]])
        (mod helper)
        (import [helper [greet]])
        (defn main [] (print (greet "world")))
    "#);

    let output1 = run_in_dir(dir.path(), "test.cl");
    assert!(output1.status.success(), "first run failed: {}", String::from_utf8_lossy(&output1.stderr));
    assert_eq!(String::from_utf8_lossy(&output1.stdout).trim(), "hello world");

    // Verify helper is cached in project cache
    let project_cache = dir.path().join(".cranelisp-cache");
    assert!(project_cache.join("helper.meta.json").exists(), "helper.meta.json should exist in project cache");

    // Second run should use cache
    let output2 = run_in_dir(dir.path(), "test.cl");
    assert!(output2.status.success(), "second run (cache) failed: {}", String::from_utf8_lossy(&output2.stderr));
    assert_eq!(String::from_utf8_lossy(&output2.stdout).trim(), "hello world");
}

#[test]
fn cache_no_cache_dir_initially() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "test.cl", "(defn main [] (pure 0))");

    // Verify no cache dirs exist before first run
    assert!(!dir.path().join(".cranelisp-cache").exists(), "project cache should not exist before first run");
    assert!(!dir.path().join("lib/.cranelisp-cache").exists(), "lib cache should not exist before first run");

    let output = run_in_dir(dir.path(), "test.cl");
    assert!(output.status.success(), "run failed: {}", String::from_utf8_lossy(&output.stderr));

    // Both should exist after first run
    assert!(dir.path().join(".cranelisp-cache").exists(), "project cache should exist after first run");
    assert!(dir.path().join("lib/.cranelisp-cache").exists(), "lib cache should exist after first run");
}

// ── REPL cache tests ──────────────────────────────────────────────────

fn run_repl_in_dir(dir: &Path, input: &str) -> std::process::Output {
    let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
        .current_dir(dir)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    use std::io::Write;
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn run_repl_with_file_in_dir(dir: &Path, filename: &str, input: &str) -> std::process::Output {
    let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
        .arg(dir.join(filename).to_str().unwrap())
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    use std::io::Write;
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn repl_cache_write_creates_files() {
    let dir = setup_cache_test_dir();
    let output = run_repl_in_dir(dir.path(), "(+ 1 2)\n");
    assert!(
        output.status.success(),
        "REPL failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Lib cache should exist with prelude
    let lib_cache = dir.path().join("lib/.cranelisp-cache");
    assert!(lib_cache.exists(), "lib .cranelisp-cache/ should exist");
    assert!(
        lib_cache.join("manifest.json").exists(),
        "lib manifest.json should exist"
    );
    assert!(
        lib_cache.join("prelude.meta.json").exists(),
        "prelude.meta.json should exist"
    );
}

#[test]
fn repl_cache_hit_second_run() {
    let dir = setup_cache_test_dir();

    // First run populates cache
    let output1 = run_repl_in_dir(dir.path(), "(+ 1 2)\n");
    assert!(
        output1.status.success(),
        "first REPL run failed: {}",
        String::from_utf8_lossy(&output1.stderr)
    );
    let lib_cache = dir.path().join("lib/.cranelisp-cache");
    assert!(lib_cache.exists(), "lib cache should exist after first run");

    // Second run should succeed (loading from cache)
    let output2 = run_repl_in_dir(dir.path(), "(+ 2 3)\n");
    assert!(
        output2.status.success(),
        "second REPL run failed: {}",
        String::from_utf8_lossy(&output2.stderr)
    );
    let stdout = String::from_utf8_lossy(&output2.stdout);
    assert!(
        stdout.contains("5"),
        "expected 5 in output, got: {}",
        stdout
    );
}

#[test]
fn repl_cache_project_module() {
    let dir = setup_cache_test_dir();
    write_source(dir.path(), "user.cl", "(defn double [x] (* 2 x))");

    let output = run_repl_with_file_in_dir(dir.path(), "user.cl", "(double 21)\n");
    assert!(
        output.status.success(),
        "REPL with file failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("42"),
        "expected 42 in output, got: {}",
        stdout
    );

    // Project cache should have user module
    let project_cache = dir.path().join(".cranelisp-cache");
    assert!(
        project_cache.exists(),
        "project .cranelisp-cache/ should exist"
    );
    assert!(
        project_cache.join("manifest.json").exists(),
        "project manifest.json should exist"
    );
    assert!(
        project_cache.join("user.meta.json").exists(),
        "user.meta.json should exist"
    );
    assert!(
        project_cache.join("user.o").exists(),
        "user.o should exist"
    );

    // Lib cache should also exist
    let lib_cache = dir.path().join("lib/.cranelisp-cache");
    assert!(
        lib_cache.exists(),
        "lib .cranelisp-cache/ should exist"
    );
}

#[test]
fn repl_restart_restores_user_definitions() {
    let dir = setup_cache_test_dir();

    // First REPL session: define a function
    let output1 = run_repl_in_dir(dir.path(), "(defn foo [x] (+ 1 x))\n");
    assert!(
        output1.status.success(),
        "first REPL session failed: {}",
        String::from_utf8_lossy(&output1.stderr)
    );
    let stdout1 = String::from_utf8_lossy(&output1.stdout);
    assert!(
        stdout1.contains("foo :: (Fn [Int] Int)"),
        "expected foo definition, got: {}",
        stdout1
    );

    // user.cl should have been written
    assert!(
        dir.path().join("user.cl").exists(),
        "user.cl should exist after first session"
    );

    // Second REPL session: call the function — should be restored
    let output2 = run_repl_in_dir(dir.path(), "(foo 5)\n");
    assert!(
        output2.status.success(),
        "second REPL session failed: {}",
        String::from_utf8_lossy(&output2.stderr)
    );
    let stdout2 = String::from_utf8_lossy(&output2.stdout);
    assert!(
        stdout2.contains("6"),
        "expected 6 from (foo 5), got stdout: {}\nstderr: {}",
        stdout2,
        String::from_utf8_lossy(&output2.stderr)
    );
}

// ── Standalone executable tests ─────────────────────────────────────────

#[test]
fn exe_build_and_run_with_platform() {
    let dir = setup_cache_test_dir();
    write_source(
        dir.path(),
        "test.cl",
        r#"
(platform stdio)
(import [platform.stdio [*]])

(defn main []
  (print "hello from exe"))
"#,
    );

    let exe_path = dir.path().join("test_exe");

    // Build the executable
    let build_output = std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
        .args([
            "--exe",
            exe_path.to_str().unwrap(),
            dir.path().join("test.cl").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        build_output.status.success(),
        "exe build failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&build_output.stdout),
        String::from_utf8_lossy(&build_output.stderr)
    );
    assert!(exe_path.exists(), "executable should exist at {:?}", exe_path);

    // Run the executable — check stdout output
    // Note: exit code is non-zero because main returns IO (heap pointer truncated to i32)
    let run_output = std::process::Command::new(&exe_path)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&run_output.stdout);
    assert!(
        stdout.contains("hello from exe"),
        "expected 'hello from exe' in stdout, got: {}\nstderr: {}",
        stdout,
        String::from_utf8_lossy(&run_output.stderr)
    );
}

#[test]
fn exe_build_and_run_without_platform() {
    let dir = setup_cache_test_dir();
    write_source(
        dir.path(),
        "test.cl",
        "(defn main [] 0)\n",
    );

    let exe_path = dir.path().join("test_exe_noplat");

    // Build the executable
    let build_output = std::process::Command::new(env!("CARGO_BIN_EXE_cranelisp"))
        .args([
            "--exe",
            exe_path.to_str().unwrap(),
            dir.path().join("test.cl").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        build_output.status.success(),
        "exe build failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&build_output.stdout),
        String::from_utf8_lossy(&build_output.stderr)
    );
    assert!(exe_path.exists(), "executable should exist at {:?}", exe_path);

    // Run the executable — exit code should be 0
    let run_output = std::process::Command::new(&exe_path)
        .output()
        .unwrap();
    assert_eq!(
        run_output.status.code(),
        Some(0),
        "expected exit code 0, got {:?}\nstdout: {}\nstderr: {}",
        run_output.status.code(),
        String::from_utf8_lossy(&run_output.stdout),
        String::from_utf8_lossy(&run_output.stderr)
    );
}
