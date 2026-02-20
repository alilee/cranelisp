//! Reference counting tests.
//!
//! These tests use global alloc/dealloc counters and MUST run single-threaded:
//!   cargo test --test rc -- --test-threads=1
//!
//! The justfile `test` recipe handles this automatically.

use cranelisp::ast::{Defn, ReplInput};
use cranelisp::ast_builder::{parse_program, parse_repl_input};
use cranelisp::codegen::{FnSlot, GotReference};
use cranelisp::error::CranelispError;
use cranelisp::jit::Jit;
use cranelisp::module::CompiledModule;
use cranelisp::names::ModuleFullPath;
use cranelisp::typechecker::TypeChecker;
use std::collections::HashMap;

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

/// Minimal REPL session for RC tests.
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
        tc.install_synthetic_bare_names();
        let mut jit = Jit::new().unwrap();
        jit.populate_builtin_func_ids(&mut tc.modules);
        let mut accumulated = HashMap::new();

        // Ensure "user" module exists and has a GOT
        let mod_path = ModuleFullPath::from("user");
        let cm = tc.modules.entry(mod_path.clone())
            .or_insert_with(|| CompiledModule::new(mod_path.clone()));
        cm.ensure_got();
        let got_addr = cm.got_table_addr().unwrap();

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
                _ => {}
            }
        }

        ReplSession { tc, jit, fn_slots: accumulated }
    }

    fn eval(&mut self, src: &str) -> Result<i64, CranelispError> {
        let input = parse_repl_input(src)?;
        match input {
            ReplInput::Expr(expr) => {
                self.tc.check_expr(&expr)?;
                let mut method_resolutions = self.tc.resolve_methods()?;
                self.tc.resolve_overloads(&mut method_resolutions)?;
                let et = self.tc.resolve_expr_types();

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
                    let slot = self.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                        .allocate_got_slot(mono.defn.span)?;
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

                self.jit.eval_expr(&expr, &method_resolutions, &et, &self.fn_slots, &self.tc.modules)
            }
            _ => panic!("expected expr, got defn"),
        }
    }
}

/// Snapshot alloc/dealloc counts, run an expression, return (allocs, deallocs, leaked).
fn rc_eval(r: &mut ReplSession, src: &str) -> (usize, usize, usize) {
    let before_alloc = cranelisp::intrinsics::alloc_count();
    let before_dealloc = cranelisp::intrinsics::dealloc_count();
    let _result = r.eval(src).unwrap();
    let new_allocs = cranelisp::intrinsics::alloc_count() - before_alloc;
    let new_deallocs = cranelisp::intrinsics::dealloc_count() - before_dealloc;
    let leaked = new_allocs - new_deallocs;
    (new_allocs, new_deallocs, leaked)
}

// ── Phase 2D: Scope-level dec ───────────────────────────────────────

#[test]
fn rc_let_string_freed_on_scope_exit() {
    // String bound in let, not returned → should be freed
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [s "hello"] 42)"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for the string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks, got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_let_string_returned_not_freed() {
    // String bound in let and returned → should NOT be freed (it's the result)
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [s "hello"] s)"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for the string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 1,
        "expected 1 leak (the return value), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_let_two_strings_one_returned() {
    // Two strings bound, one returned → only the non-returned one freed
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [s "hello" t "world"] s)"#);
    assert!(allocs >= 2, "expected at least 2 allocs, got {}", allocs);
    assert_eq!(
        leaked, 1,
        "expected 1 leak (returned string), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_nested_let_inner_scope_freed() {
    // Inner let binding freed when inner scope exits, outer binding returned
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [s "hello"] (let [t "world"] s))"#);
    assert!(allocs >= 2, "expected at least 2 allocs, got {}", allocs);
    assert_eq!(
        leaked, 1,
        "expected 1 leak (returned outer string), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_do_intermediate_freed() {
    // show 42 produces a string that is discarded (non-last in do)
    // do is now a macro — use expanded form (let [_ ...] ...) since this test harness
    // doesn't expand macros
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, "(let [_ (show 42)] 0)");
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for show string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks, got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

// ── Phase 2E: Drop glue ────────────────────────────────────────────

#[test]
fn rc_drop_glue_option_string() {
    // (Some "hello") discarded → both Some cell and inner string freed via drop glue
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [x (Some "hello")] 42)"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + Some), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks (drop glue frees inner string), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_drop_glue_nested_some() {
    // (Some (Some "hello")) → three allocations, all freed via recursive drop glue
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [x (Some (Some "hello"))] 42)"#);
    assert!(allocs >= 3, "expected at least 3 allocs, got {}", allocs);
    assert_eq!(
        leaked, 0,
        "expected zero leaks, got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_drop_glue_list_strings() {
    // (Cons "a" (Cons "b" Nil)) discarded → all Cons cells and strings freed via recursive drop glue
    // Note: list is now a macro, not parser sugar — RC test helper doesn't expand macros
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [xs (Cons "a" (Cons "b" Nil))] 42)"#);
    // Allocs: "a", "b", Cons("a", ...), Cons("b", Nil) = 4
    assert!(
        allocs >= 4,
        "expected at least 4 allocs (2 strings + 2 Cons), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks (drop glue recurses through list), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_drop_glue_none_no_crash() {
    // None is a nullary tag (not heap) → dec should be a no-op, no crash
    let mut r = ReplSession::new();
    let (_, _, leaked) = rc_eval(&mut r, "(let [x None] 42)");
    assert_eq!(leaked, 0, "None is not heap-allocated, should not leak");
}

// ── Phase 3: Vec RC ─────────────────────────────────────────────────

#[test]
fn rc_vec_int_freed_on_scope_exit() {
    // Vec of ints discarded → header + data buffer freed
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, "(let [xs [1 2 3]] 42)");
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (header + data), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks, got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_vec_string_drop_glue() {
    // Vec of strings discarded → strings freed via drop glue, then data + header freed
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [xs ["hello" "world"]] 42)"#);
    // Allocs: "hello", "world", data buffer, header = 4
    assert!(
        allocs >= 4,
        "expected at least 4 allocs (2 strings + data + header), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks (drop glue frees strings), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_vec_returned_not_freed() {
    // Vec returned → should NOT be freed (it's the result)
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, "[1 2 3]");
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (header + data), got {}",
        allocs
    );
    assert_eq!(
        leaked, 2,
        "expected 2 leaks (header + data are the return value), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_vec_empty_freed() {
    // Empty vec discarded → only header freed (no data buffer)
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, "(let [xs []] 42)");
    assert!(
        allocs >= 1,
        "expected at least 1 alloc (header), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks, got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

// ── KNOWN ISSUE: RC leak tests ──────────────────────────────────────

#[test]
fn known_issue_closure_capturing_string_leaks() {
    // KNOWN ISSUE: closure drop glue is deferred — captured heap values leak
    let mut r = ReplSession::new();
    r.eval(r#"(let [s "hello"] (fn [] s))"#).unwrap();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [s "captured"] (let [f (fn [] s)] 42))"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for string + closure, got {}",
        allocs
    );
    // Closure drop glue doesn't dec captured values, so the string leaks
    assert!(
        leaked > 0,
        "expected leaks due to deferred closure drop glue, got {} (allocs={}, deallocs={})",
        leaked,
        allocs,
        deallocs
    );
}

#[test]
fn known_issue_match_scrutinee_leaks() {
    // KNOWN ISSUE: match scrutinee not decremented after match completes.
    // The leak occurs when the scrutinee is a temporary expression (not let-bound),
    // because there is no scope-exit dec for it.
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(match (Some "hello") [None 0 (Some s) 42])"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + Some), got {}",
        allocs
    );
    // The scrutinee (Some "hello") leaks because it's not dec'd after match
    assert!(
        leaked > 0,
        "expected leaks due to scrutinee not being dec'd, got {} (allocs={}, deallocs={})",
        leaked,
        allocs,
        deallocs
    );
}

#[test]
fn known_issue_function_arg_heap_value_leaks() {
    // KNOWN ISSUE: heap-typed function arguments not decremented by callee
    let mut r = ReplSession::new();
    let input = parse_repl_input("(defn ignore-str [:String s] 42)").unwrap();
    match input {
        ReplInput::Defn(defn) => {
            r.tc.check_defn(&defn).unwrap();
            let mut mr = r.tc.resolve_methods().unwrap();
            r.tc.resolve_overloads(&mut mr).unwrap();
            let et = r.tc.resolve_expr_types();
            let scheme = r.tc.finalize_defn_type(&defn.name);
            let mod_path = ModuleFullPath::from("user");
            let got_addr = r.tc.modules.get(&mod_path).unwrap().got_table_addr().unwrap();
            let slot = r.tc.modules.get_mut(&mod_path).unwrap()
                .allocate_got_slot(defn.span).unwrap();
            let slots = fn_slots_with(&r.fn_slots, got_addr, &defn, slot);
            let meta = r.jit
                .compile_defn(&defn, &scheme, &mr, &et, slot, &slots, &r.tc.modules)
                .unwrap();
            r.tc.modules.get_mut(&ModuleFullPath::from("user")).unwrap()
                .write_got_slot(slot, meta.code_ptr);
            record_fn_slot(&mut r.fn_slots, got_addr, &defn.name, slot, defn.params.len());
        }
        _ => panic!("expected defn"),
    }
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(ignore-str "leaked")"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for string, got {}",
        allocs
    );
    // The string argument is not dec'd by the callee
    assert!(
        leaked > 0,
        "expected leaks due to callee not dec'ing arg, got {} (allocs={}, deallocs={})",
        leaked,
        allocs,
        deallocs
    );
}
