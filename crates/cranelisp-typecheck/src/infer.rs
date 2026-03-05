//! Expression type inference: one method per Expr variant.
//!
//! `infer_expr` dispatches to per-variant helpers. Each helper is typically
//! 10-40 lines, independently testable. Addresses audit HIGH-1 (monolithic infer_expr).

use std::collections::HashMap;

use cranelisp_types::{
    CranelispError, Expr, MatchArm, ModuleEntry, Pattern, ResolvedCall, Span, Symbol, Type,
    TypeExpr,
};

use crate::checker::TypeChecker;
use crate::resolve::resolve_type_expr;
use crate::scheme::mono;

impl TypeChecker {
    /// Infer the type of an expression. Main dispatch method.
    pub(crate) fn infer_expr(&mut self, expr: &Expr) -> Result<Type, CranelispError> {
        match expr {
            Expr::IntLit { span, .. } => self.infer_int_lit(*span),
            Expr::FloatLit { span, .. } => self.infer_float_lit(*span),
            Expr::BoolLit { span, .. } => self.infer_bool_lit(*span),
            Expr::Var { name, span } => self.infer_var(name, *span),
            Expr::Let {
                bindings,
                body,
                span,
            } => self.infer_let(bindings, body, *span),
            Expr::If {
                cond,
                then_branch,
                else_branch,
                span,
            } => self.infer_if(cond, then_branch, else_branch, *span),
            Expr::Lambda {
                params,
                param_annotations,
                body,
                span,
            } => self.infer_lambda(params, param_annotations, body, *span),
            Expr::Apply {
                callee,
                args,
                span,
            } => self.infer_apply(callee, args, *span),
            Expr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.infer_match(scrutinee, arms, *span),
            Expr::Annotate {
                annotation,
                expr,
                span,
            } => self.infer_annotate(annotation, expr, *span),

            // Deferred to later rings
            Expr::StringLit { span, .. } => Err(CranelispError::TypeError {
                message: "string literals not supported in Ring 0".into(),
                span: *span,
            }),
            Expr::VecLit { span, .. } => Err(CranelispError::TypeError {
                message: "vec literals not supported in Ring 0".into(),
                span: *span,
            }),
            Expr::Trace { span, .. } => Err(CranelispError::TypeError {
                message: "trace not supported in Ring 0".into(),
                span: *span,
            }),
            Expr::RunTests { span, .. } => Err(CranelispError::TypeError {
                message: "run-tests not supported in Ring 0".into(),
                span: *span,
            }),
        }
    }

    // --- Per-variant inference methods ---

    fn infer_int_lit(&mut self, span: Span) -> Result<Type, CranelispError> {
        self.record_expr_type(span, Type::Int);
        Ok(Type::Int)
    }

    fn infer_float_lit(&mut self, span: Span) -> Result<Type, CranelispError> {
        self.record_expr_type(span, Type::Float);
        Ok(Type::Float)
    }

    fn infer_bool_lit(&mut self, span: Span) -> Result<Type, CranelispError> {
        self.record_expr_type(span, Type::Bool);
        Ok(Type::Bool)
    }

    fn infer_var(&mut self, name: &Symbol, span: Span) -> Result<Type, CranelispError> {
        let scheme = self.lookup(name).ok_or_else(|| CranelispError::TypeError {
            message: format!("undefined variable: {name}"),
            span,
        })?;

        // Don't instantiate special forms -- they are not callable as values
        if let Some(ModuleEntry::Def { kind, .. }) = self.symbol_table.get(name)
            && matches!(kind.as_ref(), cranelisp_types::DefKind::SpecialForm { .. })
        {
            return Err(CranelispError::TypeError {
                message: format!("{name} is a special form, not a value"),
                span,
            });
        }

        let ty = self.instantiate(&scheme);
        let resolved = self.apply_subst(&ty);
        self.record_expr_type(span, resolved.clone());
        Ok(resolved)
    }

    // Note: creates a new scope for let bindings, preventing variable leakage
    // into enclosing scope. This deviates from plan section 2.3 but is strictly
    // better behavior.
    fn infer_let(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        self.push_scope();

        for (name, binding_expr) in bindings {
            let binding_ty = self.infer_expr(binding_expr)?;
            // Let bindings are monomorphic (spec 3.5.3)
            self.bind_local(name.clone(), mono(binding_ty));
        }

        let body_ty = self.infer_expr(body)?;
        self.pop_scope();

        let resolved = self.apply_subst(&body_ty);
        self.record_expr_type(span, resolved.clone());
        Ok(resolved)
    }

    fn infer_if(
        &mut self,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        let cond_ty = self.infer_expr(cond)?;
        self.unify(&cond_ty, &Type::Bool, cond.span())?;

        let then_ty = self.infer_expr(then_branch)?;
        let else_ty = self.infer_expr(else_branch)?;
        self.unify(&then_ty, &else_ty, span)?;

        let resolved = self.apply_subst(&then_ty);
        self.record_expr_type(span, resolved.clone());
        Ok(resolved)
    }

    fn infer_lambda(
        &mut self,
        params: &[Symbol],
        param_annotations: &[Option<TypeExpr>],
        body: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        self.push_scope();

        let mut param_types = Vec::new();
        for (i, param_name) in params.iter().enumerate() {
            let param_ty = if let Some(Some(annotation)) = param_annotations.get(i) {
                let known = self.known_type_names();
                let var_map = HashMap::new();
                resolve_type_expr(annotation, &var_map, &known, span)?
            } else {
                self.fresh_var()
            };
            param_types.push(param_ty.clone());
            self.bind_local(param_name.clone(), mono(param_ty));
        }

        let body_ty = self.infer_expr(body)?;
        self.pop_scope();

        let fn_type = Type::Fn(
            param_types
                .iter()
                .map(|t| self.apply_subst(t))
                .collect(),
            Box::new(self.apply_subst(&body_ty)),
        );
        self.record_expr_type(span, fn_type.clone());
        Ok(fn_type)
    }

    fn infer_apply(
        &mut self,
        callee: &Expr,
        args: &[Expr],
        span: Span,
    ) -> Result<Type, CranelispError> {
        let callee_ty = self.infer_expr(callee)?;

        let mut arg_types = Vec::new();
        for arg in args {
            arg_types.push(self.infer_expr(arg)?);
        }

        let ret_ty = self.fresh_var();

        // Unify callee with Fn(arg_types, ret_ty)
        let expected_fn = Type::Fn(arg_types.clone(), Box::new(ret_ty.clone()));
        self.unify(&callee_ty, &expected_fn, span)?;

        // If the callee is a named primitive, record a BuiltinFn resolution.
        // The backend uses this to emit inline Cranelift IR instead of a call.
        // No special validation needed — unification already enforces the
        // monomorphic type; any type mismatch will have been caught above.
        if let Expr::Var { name, .. } = callee
            && self.is_primitive(name)
        {
            self.method_resolutions
                .insert(span, ResolvedCall::BuiltinFn { name: name.clone() });
        }

        let resolved = self.apply_subst(&ret_ty);
        self.record_expr_type(span, resolved.clone());
        Ok(resolved)
    }

    /// Check whether a name refers to a `DefKind::Primitive` in the symbol table.
    fn is_primitive(&self, name: &str) -> bool {
        use cranelisp_types::DefKind;
        matches!(
            self.symbol_table.get(name),
            Some(cranelisp_types::ModuleEntry::Def { kind, .. })
                if matches!(kind.as_ref(), DefKind::Primitive { .. })
        )
    }

    fn infer_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        span: Span,
    ) -> Result<Type, CranelispError> {
        if arms.is_empty() {
            return Err(CranelispError::TypeError {
                message: "match expression must have at least one arm".into(),
                span,
            });
        }

        let scrutinee_ty = self.infer_expr(scrutinee)?;
        let result_ty = self.fresh_var();

        let mut covered_ctors: Vec<Symbol> = Vec::new();
        let mut has_wildcard = false;

        for arm in arms {
            self.push_scope();

            match &arm.pattern {
                Pattern::Constructor {
                    name,
                    bindings,
                    span: pat_span,
                } => {
                    self.check_constructor_pattern(
                        name,
                        bindings,
                        &scrutinee_ty,
                        *pat_span,
                    )?;
                    covered_ctors.push(name.clone());
                }
                Pattern::Wildcard { .. } => {
                    has_wildcard = true;
                }
                Pattern::Var {
                    name,
                    ..
                } => {
                    has_wildcard = true;
                    self.bind_local(name.clone(), mono(self.apply_subst(&scrutinee_ty)));
                }
            }

            let arm_ty = self.infer_expr(&arm.body)?;
            self.unify(&arm_ty, &result_ty, arm.span)?;

            self.pop_scope();
        }

        // Check exhaustiveness for concrete ADT scrutinees
        let resolved_scrutinee = self.apply_subst(&scrutinee_ty);
        if let Type::ADT(type_name, _) = &resolved_scrutinee {
            self.check_exhaustiveness(type_name, &covered_ctors, has_wildcard, span)?;
        }

        let resolved = self.apply_subst(&result_ty);
        self.record_expr_type(span, resolved.clone());
        Ok(resolved)
    }

    /// Check a constructor pattern against the scrutinee type.
    fn check_constructor_pattern(
        &mut self,
        name: &Symbol,
        bindings: &[Symbol],
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Look up the constructor in the type_defs registry
        let type_name = self
            .type_defs
            .constructor_type(name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown constructor in pattern: {name}"),
                span,
            })?
            .clone();

        // Ring 0: all constructors are nullary
        if !bindings.is_empty() {
            return Err(CranelispError::TypeError {
                message: format!(
                    "constructor {name} takes no arguments in Ring 0, got {}",
                    bindings.len()
                ),
                span,
            });
        }

        // Unify the scrutinee type with the constructor's ADT type
        let ctor_adt_type = Type::ADT(type_name, vec![]);
        self.unify(scrutinee_ty, &ctor_adt_type, span)?;

        Ok(())
    }

    fn infer_annotate(
        &mut self,
        annotation: &TypeExpr,
        expr: &Expr,
        span: Span,
    ) -> Result<Type, CranelispError> {
        let known = self.known_type_names();
        let var_map = HashMap::new();
        let ann_type = resolve_type_expr(annotation, &var_map, &known, span)?;

        let expr_ty = self.infer_expr(expr)?;
        self.unify(&expr_ty, &ann_type, span)?;

        let resolved = self.apply_subst(&ann_type);
        self.record_expr_type(span, resolved.clone());
        Ok(resolved)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{ConstructorDef, Span, TypeName, Visibility};

    fn span(start: u32, end: u32) -> Span {
        Span::new(start, end)
    }

    /// Create a TypeChecker with builtins for testing.
    fn tc() -> TypeChecker {
        TypeChecker::new()
    }

    /// Register a simple enum type for testing.
    fn register_color(tc: &mut TypeChecker) {
        tc.register_type_def(
            &TypeName::from("Color"),
            &None,
            &[],
            &[
                ConstructorDef {
                    name: Symbol::from("Red"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Green"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Blue"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }

    // --- Literal tests ---

    #[test]
    fn test_infer_int_lit() {
        let mut tc = tc();
        let expr = Expr::IntLit {
            value: 42,
            span: span(0, 2),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_float_lit() {
        let mut tc = tc();
        let expr = Expr::FloatLit {
            value: 2.72,
            span: span(0, 4),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Float);
    }

    #[test]
    fn test_infer_bool_lit() {
        let mut tc = tc();
        let expr = Expr::BoolLit {
            value: true,
            span: span(0, 4),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Bool);
    }

    // --- Var tests ---

    #[test]
    fn test_infer_var_defined() {
        let mut tc = tc();
        tc.bind_local(Symbol::from("x"), mono(Type::Int));
        let expr = Expr::Var {
            name: Symbol::from("x"),
            span: span(0, 1),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_var_undefined() {
        let mut tc = tc();
        let expr = Expr::Var {
            name: Symbol::from("x"),
            span: span(0, 1),
        };
        assert!(tc.infer_expr(&expr).is_err());
    }

    // --- Let tests ---

    #[test]
    fn test_infer_let_simple() {
        let mut tc = tc();
        // (let [x 42] x)
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("x"),
                Expr::IntLit {
                    value: 42,
                    span: span(6, 8),
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(10, 11),
            }),
            span: span(0, 12),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_let_sequential_bindings() {
        let mut tc = tc();
        // (let [x 42 y x] y)
        let expr = Expr::Let {
            bindings: vec![
                (
                    Symbol::from("x"),
                    Expr::IntLit {
                        value: 42,
                        span: span(6, 8),
                    },
                ),
                (
                    Symbol::from("y"),
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(11, 12),
                    },
                ),
            ],
            body: Box::new(Expr::Var {
                name: Symbol::from("y"),
                span: span(14, 15),
            }),
            span: span(0, 16),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    // --- If tests ---

    #[test]
    fn test_infer_if_ok() {
        let mut tc = tc();
        // (if true 1 2)
        let expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(4, 8),
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(9, 10),
            }),
            else_branch: Box::new(Expr::IntLit {
                value: 2,
                span: span(11, 12),
            }),
            span: span(0, 13),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_if_non_bool_condition() {
        let mut tc = tc();
        // (if 42 1 2) -- condition must be Bool
        let expr = Expr::If {
            cond: Box::new(Expr::IntLit {
                value: 42,
                span: span(4, 6),
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(7, 8),
            }),
            else_branch: Box::new(Expr::IntLit {
                value: 2,
                span: span(9, 10),
            }),
            span: span(0, 11),
        };
        let err = tc.infer_expr(&expr).unwrap_err();
        assert!(err.message().contains("type mismatch"));
    }

    #[test]
    fn test_infer_if_branch_mismatch() {
        let mut tc = tc();
        // (if true 1 true) -- branches must agree
        let expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(4, 8),
            }),
            then_branch: Box::new(Expr::IntLit {
                value: 1,
                span: span(9, 10),
            }),
            else_branch: Box::new(Expr::BoolLit {
                value: true,
                span: span(11, 15),
            }),
            span: span(0, 16),
        };
        assert!(tc.infer_expr(&expr).is_err());
    }

    // --- Lambda tests ---

    #[test]
    fn test_infer_lambda_identity() {
        let mut tc = tc();
        // (fn [x] x)
        let expr = Expr::Lambda {
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(8, 9),
            }),
            span: span(0, 10),
        };
        let ty = tc.infer_expr(&expr).unwrap();
        // Should be Fn([tN], tN) for some N
        match ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0], *ret);
            }
            _ => panic!("expected Fn type, got {ty:?}"),
        }
    }

    #[test]
    fn test_infer_lambda_annotated() {
        let mut tc = tc();
        // (fn [:Int x] x)
        let expr = Expr::Lambda {
            params: vec![Symbol::from("x")],
            param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(13, 14),
            }),
            span: span(0, 15),
        };
        let ty = tc.infer_expr(&expr).unwrap();
        assert_eq!(ty, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    }

    // --- Apply tests ---

    #[test]
    fn test_infer_apply_lambda() {
        let mut tc = tc();
        // ((fn [x] x) 42)
        let expr = Expr::Apply {
            callee: Box::new(Expr::Lambda {
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Box::new(Expr::Var {
                    name: Symbol::from("x"),
                    span: span(8, 9),
                }),
                span: span(1, 10),
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: span(11, 13),
            }],
            span: span(0, 14),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_apply_int_add() {
        let mut tc = tc();
        // (add-i64 1 2) -> Int
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(9, 10),
                },
                Expr::IntLit {
                    value: 2,
                    span: span(11, 12),
                },
            ],
            span: span(0, 13),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);

        // Check that a BuiltinFn resolution was recorded
        let resolution = tc.method_resolutions.get(&span(0, 13)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            _ => panic!("expected BuiltinFn resolution"),
        }
    }

    #[test]
    fn test_infer_apply_float_add() {
        let mut tc = tc();
        // (add-f64 1.0 2.0) -> Float
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-f64"),
                span: span(1, 8),
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: span(9, 12),
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: span(13, 16),
                },
            ],
            span: span(0, 17),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Float);

        let resolution = tc.method_resolutions.get(&span(0, 17)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-f64");
            }
            _ => panic!("expected BuiltinFn resolution"),
        }
    }

    #[test]
    fn test_infer_apply_int_eq() {
        let mut tc = tc();
        // (eq-i64 1 2) -> Bool
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("eq-i64"),
                span: span(1, 7),
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(8, 9),
                },
                Expr::IntLit {
                    value: 2,
                    span: span(10, 11),
                },
            ],
            span: span(0, 12),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Bool);
    }

    #[test]
    fn test_infer_apply_not() {
        let mut tc = tc();
        // (not true) -> Bool
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("not"),
                span: span(1, 4),
            }),
            args: vec![Expr::BoolLit {
                value: true,
                span: span(5, 9),
            }],
            span: span(0, 10),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Bool);

        let resolution = tc.method_resolutions.get(&span(0, 10)).unwrap();
        match resolution {
            ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "not");
            }
            _ => panic!("expected BuiltinFn resolution"),
        }
    }

    #[test]
    fn test_infer_apply_type_mismatch_int_add_float() {
        let mut tc = tc();
        // (add-i64 1.0 2.0) -- type error: float args to int primitive
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
            }),
            args: vec![
                Expr::FloatLit {
                    value: 1.0,
                    span: span(9, 12),
                },
                Expr::FloatLit {
                    value: 2.0,
                    span: span(13, 16),
                },
            ],
            span: span(0, 17),
        };
        assert!(tc.infer_expr(&expr).is_err(), "add-i64 with float args should fail");
    }

    #[test]
    fn test_infer_apply_wrong_arity() {
        let mut tc = tc();
        // (add-i64 1) -- too few args
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
            }),
            args: vec![Expr::IntLit {
                value: 1,
                span: span(9, 10),
            }],
            span: span(0, 11),
        };
        assert!(tc.infer_expr(&expr).is_err());
    }

    // --- Match tests ---

    #[test]
    fn test_infer_match_enum() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [Red 1 Green 2 Blue 3])
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Red"),
                        bindings: vec![],
                        span: span(12, 15),
                    },
                    body: Expr::IntLit {
                        value: 1,
                        span: span(16, 17),
                    },
                    span: span(12, 17),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Green"),
                        bindings: vec![],
                        span: span(18, 23),
                    },
                    body: Expr::IntLit {
                        value: 2,
                        span: span(24, 25),
                    },
                    span: span(18, 25),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Blue"),
                        bindings: vec![],
                        span: span(26, 30),
                    },
                    body: Expr::IntLit {
                        value: 3,
                        span: span(31, 32),
                    },
                    span: span(26, 32),
                },
            ],
            span: span(0, 33),
            compiler_generated: false,
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_match_non_exhaustive() {
        let mut tc = tc();
        register_color(&mut tc);

        // Match with only Red -- missing Green, Blue
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("Red"),
                    bindings: vec![],
                    span: span(12, 15),
                },
                body: Expr::IntLit {
                    value: 1,
                    span: span(16, 17),
                },
                span: span(12, 17),
            }],
            span: span(0, 18),
            compiler_generated: false,
        };
        let err = tc.infer_expr(&expr).unwrap_err();
        assert!(err.message().contains("non-exhaustive"));
    }

    #[test]
    fn test_infer_match_wildcard() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [Red 1 _ 0])
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Red"),
                        bindings: vec![],
                        span: span(12, 15),
                    },
                    body: Expr::IntLit {
                        value: 1,
                        span: span(16, 17),
                    },
                    span: span(12, 17),
                },
                MatchArm {
                    pattern: Pattern::Wildcard {
                        span: span(18, 19),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: span(20, 21),
                    },
                    span: span(18, 21),
                },
            ],
            span: span(0, 22),
            compiler_generated: false,
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_match_var_pattern() {
        let mut tc = tc();
        register_color(&mut tc);

        // (match Red [x 1]) -- var pattern binds scrutinee
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: Symbol::from("Red"),
                span: span(7, 10),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Var {
                    name: Symbol::from("x"),
                    span: span(12, 13),
                },
                body: Expr::IntLit {
                    value: 1,
                    span: span(14, 15),
                },
                span: span(12, 15),
            }],
            span: span(0, 16),
            compiler_generated: false,
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    // --- Annotate tests ---

    #[test]
    fn test_infer_annotate_matching() {
        let mut tc = tc();
        // (:Int 42) -- annotation matches
        let expr = Expr::Annotate {
            annotation: TypeExpr::Named(TypeName::from("Int")),
            expr: Box::new(Expr::IntLit {
                value: 42,
                span: span(5, 7),
            }),
            span: span(0, 8),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_annotate_mismatch() {
        let mut tc = tc();
        // (:Bool 42) -- annotation doesn't match
        let expr = Expr::Annotate {
            annotation: TypeExpr::Named(TypeName::from("Bool")),
            expr: Box::new(Expr::IntLit {
                value: 42,
                span: span(6, 8),
            }),
            span: span(0, 9),
        };
        assert!(tc.infer_expr(&expr).is_err());
    }

    // --- expr_types recording tests ---

    #[test]
    fn test_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 2);
        let expr = Expr::IntLit { value: 42, span: s };
        tc.infer_expr(&expr).unwrap();
        assert_eq!(tc.expr_types.get(&s), Some(&Type::Int));
    }

    // --- Nested expression tests ---

    #[test]
    fn test_infer_nested_arithmetic() {
        let mut tc = tc();
        // (add-i64 (add-i64 1 2) 3)
        let inner = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(9, 16),
            }),
            args: vec![
                Expr::IntLit {
                    value: 1,
                    span: span(17, 18),
                },
                Expr::IntLit {
                    value: 2,
                    span: span(19, 20),
                },
            ],
            span: span(8, 21),
        };
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("add-i64"),
                span: span(1, 8),
            }),
            args: vec![
                inner,
                Expr::IntLit {
                    value: 3,
                    span: span(23, 24),
                },
            ],
            span: span(0, 25),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }
}
