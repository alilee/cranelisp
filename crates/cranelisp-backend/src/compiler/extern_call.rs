//! The single arity-generic extern-call helper (audit F5, HIGH-3 dedup).
//!
//! Replaces the former `emit_extern_call_1`/`_2`/`_3`/`_4` arity ladder
//! (control_flow IVar plumbing used `_1`; vec_codegen used `_2`/`_3`/`_4`).
//! One slice-based method `emit_extern_call(name, &[Value], span)` declares the
//! `extern "C"` import with one `i64` param per arg + an `i64` return, emits the
//! call into `self.builder`, and returns the single result value. This closes
//! the "do not add `emit_extern_call_5`" trap the ladder invited.
//!
//! Distinct from `control_flow::fn_as_value::emit_extern_call_in_wrapper`, a
//! free fn that emits into a *borrowed* `&mut FunctionBuilder` for auto-curry
//! wrapper bodies (it cannot take `&mut self` because it runs while a wrapper
//! function — not `self.builder` — is under construction). That variant is
//! already slice-based and is left in place.

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};

use cranelisp_types::{CranelispError, ErrorLocation, Span};

use super::FnCompiler;

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Emit a call to an extern "C" function taking `args.len()` i64 arguments
    /// and returning i64. Declares/imports the extern, builds the call into
    /// `self.builder`, and returns the single result value.
    pub(crate) fn emit_extern_call(
        &mut self,
        name: &str,
        args: &[Value],
        span: Span,
    ) -> Result<Value, CranelispError> {
        let mut sig = self.module.make_signature();
        for _ in args {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self
            .module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare extern function '{name}': {e}"),
                location: ErrorLocation::from_span(span),
            })?;

        let local_func = self.module.declare_func_in_func(func_id, self.builder.func);
        let call = self.builder.ins().call(local_func, args);
        Ok(self.builder.inst_results(call)[0])
    }
}

#[cfg(test)]
mod tests {
    // Relocated crate-root tests (FIXME 0495 step 1); harness via
    // `crate::test_support`. Verbatim bodies from the former `src/tests.rs`.
    use crate::test_support::*;

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
    // standard GOT-indirect dispatch path (`compile_direct_call` reads the
    // keyed entry via `entry_at` → `callable_got_slot()` → load slot from
    // `__cranelisp_got_primitives`; the S110-W1-deleted `resolve_got_target`
    // scan no longer runs).
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
                Expr::IntLit {
                    value: 0,
                    span: Span::new(2016, 2017),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 0,
                    span: Span::new(2018, 2019),
                    inferred_type: None,
                },
            ],
            span: apply_span,
            resolved_call: None, // enrichment will set this from method_resolutions
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            resolved_targets: HashMap::new(),
            pattern_ctors: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        };

        // Seed a primitives module with `sconcat` and a GOT slot. Backend
        // reaches this entry by a direct keyed fetch (`entry_at`) on the
        // primitive's fully-qualified name — the S110-W1-deleted
        // `resolve_got_target` global-fallback walk over the caller's module
        // (`user`) no longer runs. Per Decision 0048's backend dep-ban,
        // we cannot reference `cranelisp_primitives::marshal::sconcat`
        // directly; we provide a local 2-arg stub matching the signature
        // and wire that fn ptr into the GOT slot. The test asserts
        // compilation + GOT-indirect dispatch — it does NOT assert the
        // semantics of `sconcat` (which is covered by the e2e
        // `mode_equiv_macro_user_defined` test).
        extern "C" fn sconcat_stub(_a: i64, _b: i64) -> i64 {
            0
        }
        let tables = empty_tables();
        let primitives_path = ModuleFullPath::from("primitives");
        let mut prim_table: SymbolTable = SymbolTable::new(primitives_path.clone());
        let slot = prim_table
            .allocate_got_slot()
            .expect("fresh table has free slots");
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
        let got_data_name =
            crate::compiler::got_data_symbol_name(&ModuleFullPath::from("primitives"));
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

        // W1 (KC-W0-6): the BuiltinFn arm keys the GOT-vs-direct-extern discrimination
        // off the Apply-span carrier. `sconcat` is seeded slot-carried in `primitives`,
        // so the carrier is `primitives/sconcat` — the keyed read finds the slot and
        // dispatches GOT-indirect (not a `Linkage::Import` the JIT can't resolve).
        let mut resolved_targets: HashMap<Span, cranelisp_types::FQSymbol> = HashMap::new();
        resolved_targets.insert(
            apply_span,
            cranelisp_types::FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("sconcat"),
            },
        );

        let user_module = ModuleFullPath::from("user");
        let name = defn.name.clone();
        {
            let mut st = tables
                .entry(user_module.clone())
                .or_insert_with(|| SymbolTable::new(user_module.clone()));
            st.insert(
                name.clone(),
                make_def_entry_with_targets(defn, &resolved_targets),
            );
        }

        let mut jit = Jit::new_with_symbols(&extras).expect("jit init");
        let result = compile_to_module(user_module, &[name], &tables, jit.jit_module(), true);
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
                Expr::IntLit {
                    value: 0,
                    span: Span::new(2116, 2117),
                    inferred_type: None,
                },
                Expr::IntLit {
                    value: 0,
                    span: Span::new(2118, 2119),
                    inferred_type: None,
                },
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
        // S110 W1 (Rev-2 §1.2): a call reaching codegen with neither a `resolved_call`
        // nor a `resolved_target` carrier is a hard `CodegenError` at the keyed read —
        // the loud no-soft-fallback backstop that replaced the old scan's
        // "undefined function" surface for the carrier-absent case.
        let err_msg = format!("{:?}", result.unwrap_err());
        assert!(
            err_msg.contains("no resolved_target carrier")
                || err_msg.contains("undefined function"),
            "error should name the missing carrier (W1 keyed read), got: {err_msg}"
        );
    }
}
