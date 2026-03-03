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
                            name: cranelisp::ast::mangle_impl_method(&ti.trait_name, &method.name, &target),
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

// ── Step 11: Sound RC ───────────────────────────────────────────────

#[test]
fn rc_closure_drop_glue_frees_captured_string() {
    // Closure drop glue: when a closure is freed, its captured heap values are dec'd.
    let mut r = ReplSession::new();
    r.eval(r#"(let [s "hello"] (fn [] s))"#).unwrap();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [s "captured"] (let [f (fn [] s)] 42))"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for string + closure, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "closure drop glue should free captured string (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_match_temporary_scrutinee_freed() {
    // Match on a temporary scrutinee: dec in merge block frees both the
    // constructor and its string field (via drop glue + field extraction inc).
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(match (Some "hello") [None 0 (Some s) 42])"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + Some), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "temporary scrutinee should be freed after match (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_constructor_var_arg_inc() {
    // Constructor with Var arg: (let [s "hello"] (Some s)) — the string
    // is inc'd when stored in the constructor, so it's not freed when the
    // let scope exits. The Some is returned (leaked), holding the string.
    let mut r = ReplSession::new();
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, r#"(let [s "hello"] (Some s))"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + Some), got {}",
        allocs
    );
    assert_eq!(
        leaked, 2,
        "expected 2 leaks (Some + string are the return value), got {}",
        leaked
    );
}

#[test]
fn rc_constructor_var_arg_discarded() {
    // Constructor with Var arg, discarded: both the Some and the string
    // should be freed by drop glue.
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [s "hello"] (let [_ (Some s)] 42))"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + Some), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_match_var_pattern_returns_field() {
    // Match with var pattern: extract a field from a temporary scrutinee.
    // The field is inc'd by the var pattern, scrutinee is dec'd in merge block.
    let mut r = ReplSession::new();
    let (allocs, _deallocs, leaked) =
        rc_eval(&mut r, r#"(match (Some "hello") [None "default" (Some s) s])"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + Some), got {}",
        allocs
    );
    assert_eq!(
        leaked, 1,
        "expected 1 leak (the extracted field is the return value), got {}",
        leaked
    );
}

#[test]
fn rc_closure_capturing_adt() {
    // Closure capturing an ADT value: when the closure is discarded,
    // drop glue should free the captured ADT and its contents.
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [x (Some "hello")] (let [f (fn [] x)] 42))"#);
    assert!(
        allocs >= 3,
        "expected at least 3 allocs (string + Some + closure), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "closure drop glue should free captured ADT (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_closure_capturing_closure() {
    // Closure capturing another closure: nested drop glue.
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(
        &mut r,
        r#"(let [f (fn [x] x)] (let [g (fn [] f)] 42))"#,
    );
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (inner + outer closure), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "nested closure drop glue should free all (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

// ── Consuming calling convention ────────────────────────────────────

/// Helper: define a function in the REPL session.
fn define_fn(r: &mut ReplSession, src: &str) {
    let input = parse_repl_input(src).unwrap();
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
}

#[test]
fn rc_temp_string_arg_freed() {
    // Temp string arg to cranelisp callee: callee decs param → string freed
    let mut r = ReplSession::new();
    define_fn(&mut r, "(defn ignore-str [:String s] 42)");
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(ignore-str "hello")"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "temp string arg should be freed by callee (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_nested_temp_args() {
    // Nested temps: (show (+ 1 2)) — show produces a string that is returned
    let mut r = ReplSession::new();
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, "(show 42)");
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for show string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 1,
        "show result is returned (not freed), got {}",
        leaked
    );
}

#[test]
fn rc_last_use_var_arg_consumed() {
    // Last-use Var arg: (let [s "hello"] (ignore-str s)) — s is last use,
    // ownership transfers to callee, no double-dec
    let mut r = ReplSession::new();
    define_fn(&mut r, "(defn ignore-str [:String s] 42)");
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [s "hello"] (ignore-str s))"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "last-use var should be consumed without leak (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_non_last_use_var_arg() {
    // Non-last-use Var arg: (let [s "hello"] (let [_ (ignore-str s)] s))
    // s is used after the call → inc before call, callee dec undoes inc, scope exit decs
    let mut r = ReplSession::new();
    define_fn(&mut r, "(defn ignore-str [:String s] 42)");
    let (allocs, _deallocs, leaked) =
        rc_eval(&mut r, r#"(let [s "hello"] (let [_ (ignore-str s)] s))"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 1,
        "s is returned (1 leak expected), got {}",
        leaked
    );
}

#[test]
fn rc_identity_function_return_guard() {
    // Identity function: return value == param, callee skips dec for return value
    let mut r = ReplSession::new();
    define_fn(&mut r, "(defn identity [:String s] s)");
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, r#"(identity "hello")"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 1,
        "identity return value should be alive (1 leak), got {}",
        leaked
    );
}

#[test]
fn rc_closure_call_temp_arg() {
    // Closure call with temp arg: (let [f (fn [:String s] 42)] (f "hello"))
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [f (fn [:String s] 42)] (f "hello"))"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for string + closure, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "temp arg to closure should be freed (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_multiple_temp_args() {
    // Multiple temp args in one call: both freed by callee
    let mut r = ReplSession::new();
    define_fn(&mut r, "(defn two-str [:String a :String b] 42)");
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(two-str "hello" "world")"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs for strings, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "both temp args should be freed by callee (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

// ── Compound temp arg tests (consuming convention) ──────────────────

#[test]
fn rc_compound_temp_adt_arg_freed() {
    // Consuming convention: callee takes ownership of the (Some 42) temp.
    // Callee matches on it (extracting Int, no inc needed), dec's opt at scope exit.
    // Some wrapper rc=1 → 0 → freed. Drop glue on Int field = no-op.
    let mut r = ReplSession::new();
    define_fn(
        &mut r,
        "(defn unwrap-or-zero [:(Option Int) opt] (match opt [(Some v) v None 0]))",
    );
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, "(unwrap-or-zero (Some 42))");
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for Some constructor, got {}",
        allocs
    );
    // Consuming convention frees the Some wrapper
    assert_eq!(
        leaked, 0,
        "consuming convention should free compound ADT temp, got leaked={}",
        leaked
    );
}

#[test]
fn rc_accessor_return_through_function_boundary() {
    // Consuming convention: callee owns the (Some "hello") temp.
    // Match extracts s (inc → rc=2), callee scope exit dec's opt → drop glue → dec s → rc=1.
    // Return value "hello" survives with rc=1.
    let mut r = ReplSession::new();
    define_fn(
        &mut r,
        r#"(defn unwrap-str [:(Option String) opt] (match opt [(Some s) s None ""]))"#,
    );
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, r#"(unwrap-str (Some "hello"))"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (Some + string), got {}",
        allocs
    );
    // Only the return value "hello" leaks (caller's responsibility)
    assert_eq!(
        leaked, 1,
        "expected exactly 1 leak (return value), got leaked={}",
        leaked
    );
}

#[test]
fn rc_closure_temp_arg_freed() {
    // Consuming convention: callee takes ownership of the closure temp.
    // Callee calls it, then dec's f at scope exit → rc=0 → drop glue (no heap captures).
    let mut r = ReplSession::new();
    define_fn(&mut r, "(defn call-fn [f] (f 42))");
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, "(call-fn (fn [x] x))");
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for closure, got {}",
        allocs
    );
    // Consuming convention frees the closure temp
    assert_eq!(
        leaked, 0,
        "consuming convention should free closure temp, got leaked={}",
        leaked
    );
}

// ── Liveness-based last-use optimization ────────────────────────────

#[test]
fn rc_let_alias_last_use_transfers_ownership() {
    // (let [x "hello"] (let [y x] y))
    // x is last-used in the binding of y → ownership transfers (no inc, no scope-exit dec)
    // y is returned, so 1 leaked (the return value)
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [x "hello"] (let [y x] y))"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for the string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 1,
        "expected 1 leak (return value), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_let_alias_non_last_use_still_incs() {
    // (let [x "hello"] (let [y x] x))
    // x is used after y binding (in body) → NOT last use in binding → inc emitted
    // x is returned, y is dec'd on scope exit; x survives as return value
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, r#"(let [x "hello"] (let [y x] x))"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for the string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 1,
        "expected 1 leak (return value), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_constructor_arg_last_use_transfers_ownership() {
    // (let [x "hello"] (Some x))
    // x is last-used as constructor arg → ownership transfers
    // Some wrapper leaks (compound temp), but no extra inc/dec for x
    let mut r = ReplSession::new();
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, r#"(let [x "hello"] (Some x))"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + Some), got {}",
        allocs
    );
    // Some wrapper + inner string both leak (compound temp not dec'd)
    assert!(
        leaked >= 1,
        "expected at least 1 leak, got {}",
        leaked
    );
}

#[test]
fn rc_constructor_arg_non_last_use_still_incs() {
    // (let [x "hello"] (let [y (Some x)] x))
    // x is used in body after being passed to Some → NOT last use → inc emitted
    // x returned as value, y's Some wrapper dec'd on scope exit (or leaked)
    let mut r = ReplSession::new();
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, r#"(let [x "hello"] (let [y (Some x)] x))"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + Some), got {}",
        allocs
    );
    // Return value leaks (1), Some wrapper leaks (compound temp)
    assert!(
        leaked >= 1,
        "expected at least 1 leak (return value), got {}",
        leaked
    );
}

#[test]
fn rc_branch_disables_last_use_optimization() {
    // (let [x "hello"] (if true x x))
    // x is used in both if branches → even though each branch is "last use",
    // optimization is disabled inside branches (branch_depth > 0)
    // → inc emitted for both branch uses, scope-exit dec for x
    let mut r = ReplSession::new();
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, r#"(let [x "hello"] (if true x x))"#);
    assert!(
        allocs >= 1,
        "expected at least 1 alloc for the string, got {}",
        allocs
    );
    assert_eq!(
        leaked, 1,
        "expected 1 leak (return value), got {}",
        leaked
    );
}

// ── Vec element RC + COW (Step 11H) ─────────────────────────────────

#[test]
fn rc_vec_get_string_element_survives() {
    // vec-get on Vec String: returned element gets inc'd, Vec is freed
    let mut r = ReplSession::new();
    let (allocs, _deallocs, leaked) =
        rc_eval(&mut r, r#"(let [xs ["hello" "world"]] (vec-get xs 0))"#);
    assert!(
        allocs >= 4,
        "expected at least 4 allocs (2 strings + data + header), got {}",
        allocs
    );
    // The returned string survives (1 leak), Vec + other string freed
    assert_eq!(
        leaked, 1,
        "expected 1 leak (returned string), got {} (allocs={} deallocs={})",
        leaked, allocs, _deallocs
    );
}

#[test]
fn rc_vec_get_int_no_extra_alloc() {
    // vec-get on Vec Int: no element inc needed, just return the value
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) = rc_eval(&mut r, "(let [xs [10 20 30]] (vec-get xs 1))");
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (header + data), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks (Int doesn't need RC), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_vec_set_string_elements_balanced() {
    // vec-set on Vec String: all elements properly inc'd in copy, both vecs freed
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [xs ["a" "b" "c"]] (let [ys (vec-set xs 1 "x")] 42))"#);
    assert!(
        allocs >= 6,
        "expected at least 6 allocs (3 orig strings + 1 new string + 2 headers + 2 data), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks (all elements + vecs freed), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_vec_push_string_elements_balanced() {
    // vec-push on Vec String: all copied elements inc'd, both vecs freed
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [xs ["a" "b"]] (let [ys (vec-push xs "c")] 42))"#);
    assert!(
        allocs >= 5,
        "expected at least 5 allocs (2 orig + 1 new string + 2 headers + 2 data), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks (all elements + vecs freed), got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

#[test]
fn rc_vec_set_cow_last_use() {
    // vec-set at last use with unique Vec: COW mutates in place
    let mut r = ReplSession::new();
    let result = r.eval("(let [xs [1 2 3]] (vec-get (vec-set xs 0 99) 0))").unwrap();
    assert_eq!(result, 99, "COW vec-set should produce correct value");
}

#[test]
fn rc_vec_set_shared_copies() {
    // vec-set when Vec is shared: must copy, both vecs survive independently
    let mut r = ReplSession::new();
    // xs is shared (used after vec-set as return value), so vec-set must copy
    let result = r.eval("(let [xs [1 2 3]] (let [ys (vec-set xs 0 99)] (vec-get xs 0)))").unwrap();
    assert_eq!(result, 1, "original vec should be unchanged when shared");
}

#[test]
fn rc_vec_push_cow_last_use() {
    // vec-push at last use: COW pushes in place (if capacity) or reallocs
    let mut r = ReplSession::new();
    let result = r.eval("(let [xs [1 2]] (vec-get (vec-push xs 3) 2))").unwrap();
    assert_eq!(result, 3, "COW vec-push should produce correct value");
}

#[test]
fn rc_vec_nested_string_ops() {
    // String from vec-get stored via vec-set: no leaks
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [xs ["a" "b"]] (let [ys (vec-set xs 0 (vec-get xs 1))] 42))"#);
    assert!(
        allocs >= 4,
        "expected at least 4 allocs, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "expected zero leaks, got {} (allocs={}, deallocs={})",
        leaked, allocs, deallocs
    );
}

// ── Uniqueness tracking + borrowed reads (Step 11J-K) ───────────────

#[test]
fn rc_borrowed_read_from_unique_vec() {
    // vec-get on unique Vec String: element is borrowed (no inc), Vec freed by drop glue.
    // Element survives because borrowed read auto-upgrades when returned as result.
    let mut r = ReplSession::new();
    let (allocs, _deallocs, leaked) =
        rc_eval(&mut r, r#"(let [xs ["hello" "world"]] (vec-get xs 0))"#);
    assert!(
        allocs >= 4,
        "expected at least 4 allocs (2 strings + data + header), got {}",
        allocs
    );
    // Returned string survives, everything else freed
    assert_eq!(
        leaked, 1,
        "expected 1 leak (returned string), got {}",
        leaked
    );
}

#[test]
fn rc_borrowed_read_vec_int_no_crash() {
    // vec-get on unique Vec Int: Int elements are NeverHeap, borrowed read is a no-op
    let mut r = ReplSession::new();
    let result = r.eval("(let [xs [10 20 30]] (vec-get xs 1))").unwrap();
    assert_eq!(result, 20, "should read correct Int element");
}

#[test]
fn rc_borrowed_read_passed_to_consuming_call() {
    // Borrowed string from vec-get passed to consuming fn call:
    // auto-upgrade emits inc, callee dec's → balanced
    let mut r = ReplSession::new();
    define_fn(&mut r, "(defn ignore-str [:String s] 42)");
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [xs ["hello" "world"]] (ignore-str (vec-get xs 0)))"#);
    assert!(
        allocs >= 4,
        "expected at least 4 allocs, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "borrowed read + consuming call should be balanced (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_borrowed_match_field_extraction() {
    // Match on unique scrutinee: field extracted as borrowed, used in body.
    // Scrutinee is consumed by the consuming convention, field borrowed from it.
    let mut r = ReplSession::new();
    define_fn(
        &mut r,
        r#"(defn unwrap-str [:(Option String) opt] (match opt [(Some s) s None ""]))"#,
    );
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, r#"(unwrap-str (Some "hello"))"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + Some), got {}",
        allocs
    );
    // Return value "hello" survives
    assert_eq!(
        leaked, 1,
        "expected 1 leak (returned string), got {}",
        leaked
    );
}

#[test]
fn rc_unique_vec_set_static_cow() {
    // Static COW: unique Vec + last-use → mutate in place without runtime rc check
    let mut r = ReplSession::new();
    let result = r.eval("(let [xs [1 2 3]] (vec-get (vec-set xs 0 99) 0))").unwrap();
    assert_eq!(result, 99, "static COW vec-set should produce correct value");
    // Also verify no leaks
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, "(let [xs [1 2 3]] (let [ys (vec-set xs 0 99)] 42))");
    assert_eq!(
        leaked, 0,
        "static COW vec-set should not leak (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_unique_vec_push_static_cow() {
    // Static COW: unique Vec + last-use → push in place without runtime rc check
    let mut r = ReplSession::new();
    let result = r.eval("(let [xs [1 2]] (vec-get (vec-push xs 3) 2))").unwrap();
    assert_eq!(result, 3, "static COW vec-push should produce correct value");
    // Verify no leaks
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, "(let [xs [1 2]] (let [ys (vec-push xs 3)] 42))");
    assert_eq!(
        leaked, 0,
        "static COW vec-push should not leak (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_non_unique_vec_still_copies() {
    // Non-unique Vec (used after set): must copy, original unchanged
    let mut r = ReplSession::new();
    let result = r
        .eval("(let [xs [1 2 3]] (let [ys (vec-set xs 0 99)] (vec-get xs 0)))")
        .unwrap();
    assert_eq!(result, 1, "shared Vec should be unchanged after vec-set");
}

#[test]
fn rc_borrowed_read_in_extern_call() {
    // Borrowed string from unique Vec used in extern call (show is extern).
    // Extern calls use borrowed convention — no dec for borrowed temp.
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [xs ["hello" "world"]] (let [_ (show (vec-get xs 0))] 42))"#);
    assert!(
        allocs >= 4,
        "expected at least 4 allocs, got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "borrowed read in extern call should be balanced (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

// ── Gap 1: Closures returned from functions / stored in ADTs ─────────

#[test]
fn rc_closure_escaping_creating_scope() {
    // A function that returns a closure: the closure's captured string must
    // remain alive after the creating function returns.
    let mut r = ReplSession::new();
    define_fn(&mut r, r#"(defn make-greeter [:String name] (fn [] name))"#);
    // make-greeter allocates a string and returns a closure capturing it.
    // The closure (1 alloc for env) and the string (1 alloc) leak as the return value.
    let (allocs, _deallocs, leaked) = rc_eval(&mut r, r#"(make-greeter "world")"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + closure env), got {}",
        allocs
    );
    // The returned closure (and its captured string) leaks — that is correct:
    // the result is owned by the caller.
    assert!(
        leaked >= 1,
        "expected at least 1 leak (the returned closure), got {}",
        leaked
    );
}

#[test]
fn rc_closure_from_function_discarded() {
    // Return a closure from a function, then immediately discard it.
    // Both the closure env and the captured string should be freed.
    let mut r = ReplSession::new();
    define_fn(&mut r, r#"(defn make-adder [:String label] (fn [x] x))"#);
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [f (make-adder "tag")] 42)"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (string + closure), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "discarded closure should be freed with its captures (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_closure_stored_in_adt() {
    // Closure stored as a field in an ADT constructor.
    // When the ADT is discarded, drop glue should free the closure env.
    let mut r = ReplSession::new();
    // (Some (fn [] 42)) — the closure has no heap captures but allocates an env cell.
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [x (Some (fn [] 42))] 42)"#);
    assert!(
        allocs >= 2,
        "expected at least 2 allocs (closure + Some), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "closure stored in ADT should be freed by drop glue (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

#[test]
fn rc_closure_with_string_stored_in_adt() {
    // Closure capturing a string, stored in an ADT.
    // Dropping the ADT should free: Some cell, closure env, captured string.
    let mut r = ReplSession::new();
    let (allocs, deallocs, leaked) =
        rc_eval(&mut r, r#"(let [s "captured"] (let [x (Some (fn [] s))] 42))"#);
    assert!(
        allocs >= 3,
        "expected at least 3 allocs (string + closure + Some), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "ADT drop glue should free closure and its captured string (allocs={}, deallocs={})",
        allocs, deallocs
    );
}

// ── Gap 2: User-defined recursive ADTs with drop glue ────────────────

#[test]
fn rc_user_recursive_adt_mylist_eval() {
    // Define a user-owned linked list type and verify it evaluates correctly.
    let mut r = ReplSession::new();
    // Register the type via parse_program + register_type_def
    {
        use cranelisp::ast::TopLevel;
        use cranelisp::ast_builder::parse_program;
        let src = "(deftype (MyList a) MyNil (MyCons [:a val :(MyList a) rest]))";
        let items = parse_program(src).unwrap();
        for item in &items {
            if matches!(item, TopLevel::TypeDef { .. }) {
                r.tc.register_type_def(item);
            }
        }
        r.jit.register_type_defs(&r.tc);
    }
    // Build a three-node list and verify it evaluates (returns a heap pointer != 0).
    let result = r.eval("(MyCons 1 (MyCons 2 (MyCons 3 MyNil)))");
    assert!(
        result.is_ok(),
        "user-defined recursive ADT should evaluate: {:?}",
        result
    );
    let val = result.unwrap();
    // A data constructor returns a heap pointer (non-zero, tag at offset 0 = 1 for MyCons).
    assert_ne!(val, 0, "MyCons should return a non-null heap pointer");
}

#[test]
fn rc_user_recursive_adt_drop_glue() {
    // A discarded MyList with string values must have zero leaks.
    let mut r = ReplSession::new();
    {
        use cranelisp::ast::TopLevel;
        use cranelisp::ast_builder::parse_program;
        let src = "(deftype (MyList a) MyNil (MyCons [:a val :(MyList a) rest]))";
        let items = parse_program(src).unwrap();
        for item in &items {
            if matches!(item, TopLevel::TypeDef { .. }) {
                r.tc.register_type_def(item);
            }
        }
        r.jit.register_type_defs(&r.tc);
    }
    // Build and discard a two-node list of strings.
    // Allocs: "a" string, MyCons("a",…), "b" string, MyCons("b", MyNil) = 4
    let (allocs, deallocs, leaked) = rc_eval(
        &mut r,
        r#"(let [xs (MyCons "a" (MyCons "b" MyNil))] 42)"#,
    );
    assert!(
        allocs >= 4,
        "expected at least 4 allocs (2 strings + 2 MyCons), got {}",
        allocs
    );
    assert_eq!(
        leaked, 0,
        "user-defined recursive ADT drop glue must free all nodes (allocs={}, deallocs={})",
        allocs, deallocs
    );
}
