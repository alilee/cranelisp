//! RC / drop-glue emission and the heap classification it keys on.
//!
//! This is the single home for the heap-class match (`signature_heap_category`)
//! that the plan's duplicates and drops and the match seam's field typing read,
//! and of [`FnCompiler::emit_typed_rc_dec`], the ONE canonical glue-call
//! emitter every concrete release goes through. The pure type helper
//! `find_var_type_in_expr` lives here too.

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::{
    ConcreteType, CranelispError, ModuleFullPath, MonoExpr, Symbol, SymbolTable, Type,
};

use crate::heap::{self, HeapCategory};

use super::FnCompiler;
use super::census::{self, Record, Shape};

/// Release a CLOSURE box through its **embedded** `DROP_GLUE_PTR` — the
/// borrowed-builder body of [`FnCompiler::emit_closure_dec_inline`].
///
/// A closure box OWNS its captures, and the only thing that knows how to
/// release them is the glue pointer the allocating site stored in the box: a
/// bare `heap::emit_rc_dec(.., None)` frees the box and STRANDS everything
/// under it. Emission: `atomic dec` → on rc→0 `fence`, load
/// `DROP_GLUE_PTR`, `call_indirect` it when non-zero, then `dealloc`.
///
/// Free-fn form because the two capture drop-glue mirrors build their bodies in
/// a SEPARATE Cranelift context, not `self.builder` (the `emit_capture_inc_into`
/// precedent). One body, two callers (Principle 7).
pub(crate) fn emit_closure_dec_into<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    closure_val: Value,
    dealloc_id: FuncId,
) {
    use crate::heap::HeapClosure;
    use cranelift_codegen::ir::AtomicRmwOp;
    use cranelisp_types::HeapHeader;

    let cont_block = builder.create_block();

    // Decrement RC.
    let rc_addr = builder
        .ins()
        .iadd_imm(closure_val, i64::from(HeapHeader::RC_OFFSET));
    let one = builder.ins().iconst(types::I64, 1);
    let old_rc = builder.ins().atomic_rmw(
        types::I64,
        MemFlags::trusted(),
        AtomicRmwOp::Sub,
        rc_addr,
        one,
    );

    // Branch: if old_rc == 1, free the closure.
    let cmp = builder.ins().icmp(IntCC::Equal, old_rc, one);
    let free_block = builder.create_block();
    builder.ins().brif(cmp, free_block, &[], cont_block, &[]);

    // Free path.
    builder.switch_to_block(free_block);
    builder.seal_block(free_block);
    builder.ins().fence();

    // Load drop_glue_ptr from the closure.
    let drop_glue_ptr = heap::heap_load(builder, closure_val, HeapClosure::DROP_GLUE_PTR_OFFSET);

    // If drop_glue_ptr != 0, call it.
    let zero = builder.ins().iconst(types::I64, 0);
    let has_glue = builder.ins().icmp(IntCC::NotEqual, drop_glue_ptr, zero);
    let glue_block = builder.create_block();
    let dealloc_block = builder.create_block();
    builder
        .ins()
        .brif(has_glue, glue_block, &[], dealloc_block, &[]);

    // Call drop glue: (closure_ptr: i64) -> ()
    builder.switch_to_block(glue_block);
    builder.seal_block(glue_block);

    let mut glue_sig = module.make_signature();
    glue_sig.params.push(AbiParam::new(types::I64));
    let glue_sig_ref = builder.import_signature(glue_sig);
    builder
        .ins()
        .call_indirect(glue_sig_ref, drop_glue_ptr, &[closure_val]);
    builder.ins().jump(dealloc_block, &[]);

    // Dealloc the closure.
    builder.switch_to_block(dealloc_block);
    builder.seal_block(dealloc_block);
    let dealloc_ref = module.declare_func_in_func(dealloc_id, builder.func);
    builder.ins().call(dealloc_ref, &[closure_val]);
    builder.ins().jump(cont_block, &[]);

    // Continue.
    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// **The ONE release emitter** (S118 slice S1,
    /// `design/backend/transitive-drop-glue.md` §4): classify `ty`, and for an
    /// owned heap value emit exactly ONE `call` to the canonical
    /// per-concrete-type drop glue.
    ///
    /// What is deliberately NOT here:
    ///
    /// - **No recursive field inspection.** The body the registry emits walks
    ///   the type's own owned graph, so this seam has no depth and no cutoff.
    /// - **No `needs_guard` parameter.** The nullary-tag guard is a property of
    ///   the concrete TYPE (`GlueShape::guard_nullary`, derived from the type's
    ///   own constructor set) and lives once inside the glue body. A site
    ///   parameter is the last place a *site* could disagree with a *type* about
    ///   how a value is released, which is why removing it is part of the
    ///   migration rather than a tidy.
    /// - **No fallback arm.** A release site that cannot supply a
    ///   [`ConcreteType`] is a located compilation error (design §3.4 D2): a
    ///   non-concrete key at a *release* site means a producer gap, and a
    ///   shallow dec there is exactly the silent, site-dependent change of
    ///   release semantics the depth cutoff used to make.
    ///
    /// Non-owning representations (`NeverHeap`/`Value`) are a no-op — the
    /// registry's `request_if_owning` is the single membership filter.
    pub(crate) fn emit_typed_rc_dec(
        &mut self,
        val: Value,
        ty: &Type,
    ) -> Result<(), CranelispError> {
        let concrete = ConcreteType::from_type(ty)
            .map_err(|_| release_site_type_error(self.current_fn_name.as_ref(), ty))?;
        let Some(glue_id) =
            self.glue
                .request_if_owning(self.module, self.ctx.symbol_tables, concrete)?
        else {
            return Ok(());
        };
        let glue_ref = self.module.declare_func_in_func(glue_id, self.builder.func);
        self.builder.ins().call(glue_ref, &[val]);
        Ok(())
    }

    /// Emit RC dec for a closure value using its embedded drop glue pointer.
    ///
    /// Unlike `emit_rc_dec` which takes a compile-time `drop_glue_id`,
    /// this loads the drop glue pointer from the closure's embedded
    /// `DROP_GLUE_PTR_OFFSET` field at runtime and calls it if non-zero.
    ///
    /// Used for:
    /// - Closure parameters received from callers (type unknown at compile time)
    /// - Temporary closure expressions used as callees
    /// - Any closure variable where the static drop glue is not available
    pub(crate) fn emit_closure_dec_inline(&mut self, closure_val: Value, dealloc_id: FuncId) {
        emit_closure_dec_into(&mut self.builder, self.module, closure_val, dealloc_id);
    }
}

/// The D2 located error: a release site reached with a type that is not
/// concrete. Names the type AND the requesting function, because the fix is
/// always upstream of this seam (a typecheck producer gap), never a
/// backend-side fallback. Free fn so the whole diagnostic is unit-testable
/// without a live `FnCompiler`.
pub(crate) fn release_site_type_error(fn_name: Option<&Symbol>, ty: &Type) -> CranelispError {
    CranelispError::CodegenError {
        message: format!(
            "release site in '{}' reached a non-concrete type {ty:?}; canonical drop \
             glue is keyed on the concrete type and there is no shallow fallback \
             (design/backend/transitive-drop-glue.md §3.4 D2)",
            fn_name
                .map(|s| s.to_string())
                .unwrap_or_else(|| "<anonymous body>".into()),
        ),
        location: cranelisp_types::ErrorLocation::from_span(cranelisp_types::Span::SYNTHETIC),
    }
}

// `TypedRelease` / `typed_release_kind` (FIXME 0753's per-site teardown
// classification) are DELETED at S118 slice S1: the registry's own
// `GlueShape` classification subsumes them, and the teardown now lives inside
// the generated body rather than at the site. The load-bearing half of that
// rule — Vec is classified BEFORE ADT, because a Vec IS spelled
// `Type::ADT(Vec, [t])` but its elements live behind `DATA_PTR` — is rehomed
// onto `drop_glue::GlueShape` and pinned by
// `drop_glue::tests::a_vec_shape_is_not_classified_as_a_plain_adt`.

// --- Free helper functions for type variable resolution ---

/// Find the inferred type of a Var reference with the given name in an expression tree.
///
/// Walks the AST recursively and returns the first Var node's `inferred_type()`
/// that matches the name. Used by `derive_param_type_from_body` to find parameter
/// types from use sites when the defn-level type is not available.
pub(crate) fn find_var_type_in_expr(expr: &MonoExpr, name: &Symbol) -> Option<Type> {
    match expr {
        MonoExpr::Var {
            name: var_name, ty, ..
        } if var_name == name => Some(ty.to_type()),
        MonoExpr::Let { bindings, body, .. } => {
            for (_, val) in bindings {
                if let Some(ty) = find_var_type_in_expr(val, name) {
                    return Some(ty);
                }
            }
            find_var_type_in_expr(body, name)
        }
        MonoExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => find_var_type_in_expr(cond, name)
            .or_else(|| find_var_type_in_expr(then_branch, name))
            .or_else(|| find_var_type_in_expr(else_branch, name)),
        MonoExpr::Lambda { body, .. } => find_var_type_in_expr(body, name),
        MonoExpr::Apply { callee, args, .. } => find_var_type_in_expr(callee, name)
            .or_else(|| args.iter().find_map(|a| find_var_type_in_expr(a, name))),
        MonoExpr::Match {
            scrutinee, arms, ..
        } => find_var_type_in_expr(scrutinee, name).or_else(|| {
            arms.iter()
                .find_map(|arm| find_var_type_in_expr(&arm.body, name))
        }),
        MonoExpr::VecLit { elements, .. } => {
            elements.iter().find_map(|e| find_var_type_in_expr(e, name))
        }
        MonoExpr::Trace { body, .. } => find_var_type_in_expr(body, name),
        MonoExpr::ParBind { bindings, body, .. } => {
            for (_, val) in bindings {
                if let Some(ty) = find_var_type_in_expr(val, name) {
                    return Some(ty);
                }
            }
            find_var_type_in_expr(body, name)
        }
        // A `LaunchContinue` node's `launched` sub-tree (the detached
        // per-connection handler) is where a continuation parameter is often
        // used EXCLUSIVELY — e.g. `conn` in `(bind (read-conn conn) (fn [req]
        // … (send-conn conn …)))`. Without this arm such a parameter has no
        // recorded type, so its duplicates and drops classify it as owning no
        // heap (FIXME 0494 bug #2, the size-32 `Connection` stale RC-dec).
        MonoExpr::LaunchContinue {
            launched,
            continuation,
            ..
        } => find_var_type_in_expr(launched, name)
            .or_else(|| find_var_type_in_expr(continuation, name)),
        MonoExpr::ConstrADT { fields, .. } => {
            fields.iter().find_map(|f| find_var_type_in_expr(f, name))
        }
        // Literals carry no sub-expression and no variable reference — no type
        // to find. This arm is deliberately EXHAUSTIVE (not `_ => None`) so that
        // adding a new `MonoExpr` variant carrying a sub-expression is a compile
        // error at this seam, forcing a conscious traversal decision. A silent
        // `_ => None` here is exactly how FIXME 0494's double-free shipped
        // (a `conn`-typed param used only inside a then-missing `LaunchContinue`
        // sub-tree fell through to `None` → skipped consuming inc → UAF). Kept
        // in lock-step with its two exhaustive sibling MonoExpr RC/lifetime
        // traversals (`heap.rs::collect_var_uses`,
        // `control_flow/free_vars.rs::collect_free_vars`); all three must stay
        // exhaustive.
        //
        // `Var { .. }` also lands here: the guarded `Var` arm above returns the
        // type only when the name matches (a guarded arm does not count toward
        // exhaustivity), so a non-matching `Var` yields no type.
        MonoExpr::Var { .. }
        | MonoExpr::IntLit { .. }
        | MonoExpr::FloatLit { .. }
        | MonoExpr::BoolLit { .. }
        | MonoExpr::StringLit { .. } => None,
    }
}

/// Heap-classify a SIGNATURE-PATH field/binding `Type` (concrete-boundary-type.md
/// §3.1.1, FIXME 0391; the residual-`Var` arm's authority is
/// `design/backend/non-concrete-release-contract.md` §2.3 and §4). The body-AST codegen walk
/// classifies a `ConcreteType`
/// off each `MonoExpr` node directly — no `Var` by construction. But the
/// `Type`-typed RC machinery (binder types, `CtorField`, `resolve_field_types`)
/// reads field/binding types from the **signature** (the `scheme`, `Type::Fn`
/// params), where a `Var` does survive.
///
/// **Families reaching this classification with a residual variable.** The
/// census's authoritative home is the `FnCompiler::emit_release` rustdoc,
/// including its do-not-re-run-the-experiment warning. In brief:
///
/// 1. **A constructor template's own parameter** (`(deftype (Option a) …
///    (Some [:a val]))` gives the template a `Type::Var` field param). In
///    production this face is closed by representation — a residual-parameter
///    constructor is a slotless `Life::Template` and never reaches codegen
///    (contract §4.1, I-CT′); only directly constructed unit-test frames still
///    reach it.
/// 2. A **constructor field** read inside a concrete body: `CtorMeta`'s field
///    types come from the declaration's scheme, so a generic product's field
///    is a `Type::Var` at every use site (contract §7.4).
/// 3. The S119 families, synthetic field accessors of a generic product and
///    generic trait-method instances, as producer obligations under FIXME 0903
///    (contract §4.2). No codegen frame's parameter is residual-typed: a target
///    is a `Life::Concrete` body, whose slot exists only for a concrete scheme.
///
/// So this helper classifies a concrete field type via the total
/// `HeapCategory::classify(&ConcreteType, …)`, and maps a residual `Var`/`TyConApp`
/// to `Mixed` — the uniform-representation category, since the runtime
/// representation of any of the three is a uniform i64 tag-or-pointer. It does
/// NOT widen the `ConcreteType` `classify` (which stays total, no `Var` arm).
///
/// Classifying such a binding heap-typed is what routes it to a release seam at
/// all; whether the release is then legal is a separate question, answered at
/// `FnCompiler::emit_release`. **That arm is keyed on the TYPE, not the frame**
/// — knowingly (FIXME 0903). A frame key was measured at **+16 hard codegen
/// refusals** over the `spec_*` corpus, which is how families 2 and 3 above
/// were found.
pub(crate) fn signature_heap_category<C, L>(
    ty: &Type,
    symbol_tables: Option<&dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>>>,
    census_frame: &census::Frame,
) -> HeapCategory
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    match ConcreteType::from_type(ty) {
        Ok(ct) => HeapCategory::classify(&ct, symbol_tables),
        // A residual signature `Var` — any of the THREE measured families above
        // (ctor-template field param, synthetic field accessor's `self`, generic
        // trait-method instance) — or an unresolved HKT head: uniform i64
        // representation → `Mixed` (the guarded RC path).
        // `design/backend/transitive-drop-glue.md` §4.1 + FIXME 0903.
        Err(_) => {
            census::record(census_frame, || Record::Retain(Shape::of_residual(ty)));
            HeapCategory::Mixed
        }
    }
}

#[cfg(test)]
mod find_var_type_tests {
    use super::find_var_type_in_expr;
    use cranelisp_types::{
        ConcreteType, FQTypeName, ModuleFullPath, MonoExpr, Span, Symbol, TypeName,
    };

    fn conn_ty() -> ConcreteType {
        // A 1-field heap ADT, mirroring `web/Connection` (FIXME 0494 bug #2).
        ConcreteType::ADT(
            FQTypeName::new(ModuleFullPath::from("web"), TypeName::from("Connection")),
            vec![],
        )
    }

    fn var(name: &str, ty: ConcreteType) -> MonoExpr {
        MonoExpr::Var {
            resolution: cranelisp_types::VarRef::Local {
                binder: Symbol::from(name),
                binding_span: Span::SYNTHETIC,
            },
            name: Symbol::from(name),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty,
        }
    }

    fn apply(callee: MonoExpr, args: Vec<MonoExpr>) -> MonoExpr {
        MonoExpr::Apply {
            dispatch: cranelisp_types::ApplyRef::ViaCallee,
            callee: Box::new(callee),
            args,
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::Int,
            confined: None,
            escapes: None,
            provenance: None,
            unique_static: None,
        }
    }

    // spec: bounded-contexts.md §4b invariant 15 / ring2-rc.md §5.5 — a continuation
    // parameter used ONLY inside a launched (detached) sub-tree must still be
    // heap-typed so its consuming inc balances the poll state-closure drop-glue dec.
    // RED before the FIXME-0494 fix: `find_var_type_in_expr` had no `LaunchContinue`
    // arm, so it returned `None` for `conn` here and the consuming inc was skipped →
    // double-free of the borrowed `Connection`.
    #[test]
    fn find_var_type_descends_into_launchcontinue_launched_subtree() {
        // `(launch (read-conn conn) <continuation>)` — `conn` (a heap ADT) is used
        // ONLY inside the launched (detached) branch, never in the continuation.
        let launched = apply(
            var("read-conn", ConcreteType::Int),
            vec![var("conn", conn_ty())],
        );
        let continuation = var("_", ConcreteType::Int);
        let node = MonoExpr::LaunchContinue {
            launched: Box::new(launched),
            continuation: Box::new(continuation),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        };

        let found = find_var_type_in_expr(&node, &Symbol::from("conn"));
        assert_eq!(
            found,
            Some(conn_ty().to_type()),
            "conn used only in a LaunchContinue.launched sub-tree must still be \
             heap-typed (else its consuming inc is skipped → poll drop-glue double-free)"
        );
    }

    // A temporary (a non-`Var` sub-expression) inside the launched sub-tree is NOT a
    // named variable, so it is (correctly) not discovered as a param type — the
    // owned-temporary side of the borrowed-vs-owned discipline (no inc owed).
    #[test]
    fn find_var_type_absent_for_unnamed_var() {
        let launched = apply(
            var("read-conn", ConcreteType::Int),
            vec![var("conn", conn_ty())],
        );
        let node = MonoExpr::LaunchContinue {
            launched: Box::new(launched),
            continuation: Box::new(var("_", ConcreteType::Int)),
            span: Span::SYNTHETIC,
            ty: ConcreteType::Int,
        };
        // A name not present anywhere resolves to None (no spurious type).
        assert_eq!(find_var_type_in_expr(&node, &Symbol::from("nope")), None);
    }
}

/// S118 slice S1 — the canonical glue-call emitter (§10 row 3).
#[cfg(test)]
mod glue_call_emitter_tests;
