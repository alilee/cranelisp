//! Expression type inference: one method per Expr variant.
//!
//! `infer_expr` dispatches to per-variant helpers. Each helper is typically
//! 10-40 lines, independently testable. Addresses audit HIGH-1 (monolithic infer_expr).

use std::collections::HashMap;

use cranelisp_types::{
    CranelispError, Expr, MatchArm, ModuleEntry, Pattern, ResolvedCall, Scheme, Span, Symbol,
    Type, TypeExpr,
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

            Expr::StringLit { span, .. } => self.infer_string_lit(*span),
            Expr::VecLit { elements, span } => self.infer_vec_lit(elements, *span),
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

    fn infer_string_lit(&mut self, span: Span) -> Result<Type, CranelispError> {
        self.record_expr_type(span, Type::String);
        Ok(Type::String)
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
    ///
    /// For nullary constructors, validates no bindings and unifies with ADT type.
    /// For data constructors, instantiates the polymorphic constructor scheme,
    /// unifies the result type with the scrutinee, and binds pattern variables
    /// to the instantiated field types.
    fn check_constructor_pattern(
        &mut self,
        name: &Symbol,
        bindings: &[Symbol],
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        // Look up the constructor's scheme from the symbol table
        let ctor_scheme = self.lookup_constructor_scheme(name, span)?;

        // Instantiate the scheme with fresh type variables
        let instantiated = self.instantiate(&ctor_scheme);

        // Unify and bind depending on whether the constructor has fields
        self.unify_pattern_with_scrutinee(
            name, bindings, &instantiated, scrutinee_ty, span,
        )
    }

    /// Look up a constructor's type scheme from the symbol table.
    fn lookup_constructor_scheme(
        &self,
        name: &Symbol,
        span: Span,
    ) -> Result<Scheme, CranelispError> {
        // Verify the constructor exists in the type registry
        let _type_name = self
            .type_defs
            .constructor_type(name)
            .ok_or_else(|| CranelispError::TypeError {
                message: format!("unknown constructor in pattern: {name}"),
                span,
            })?;

        // Get the scheme from the symbol table
        self.lookup(name).ok_or_else(|| CranelispError::TypeError {
            message: format!("constructor {name} has no type scheme"),
            span,
        })
    }

    /// Unify an instantiated constructor type with the scrutinee and bind variables.
    fn unify_pattern_with_scrutinee(
        &mut self,
        name: &Symbol,
        bindings: &[Symbol],
        instantiated: &Type,
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        match instantiated {
            // Nullary constructor: type is just the ADT type
            Type::ADT(..) => {
                if !bindings.is_empty() {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "constructor {name} takes no arguments, got {}",
                            bindings.len()
                        ),
                        span,
                    });
                }
                self.unify(scrutinee_ty, instantiated, span)
            }

            // Data constructor: type is Fn([field_types], adt_type)
            Type::Fn(field_types, ret_type) => {
                self.bind_data_ctor_pattern(
                    name, bindings, field_types, ret_type, scrutinee_ty, span,
                )
            }

            _ => Err(CranelispError::TypeError {
                message: format!(
                    "constructor {name} has unexpected type: {instantiated}"
                ),
                span,
            }),
        }
    }

    /// Bind pattern variables for a data constructor with fields.
    fn bind_data_ctor_pattern(
        &mut self,
        name: &Symbol,
        bindings: &[Symbol],
        field_types: &[Type],
        ret_type: &Type,
        scrutinee_ty: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        if bindings.len() != field_types.len() {
            return Err(CranelispError::TypeError {
                message: format!(
                    "constructor {name} expects {} field(s), got {} binding(s)",
                    field_types.len(),
                    bindings.len()
                ),
                span,
            });
        }

        // Unify the constructor's result type with the scrutinee
        self.unify(scrutinee_ty, ret_type, span)?;

        // Bind each pattern variable to the resolved field type
        for (binding_name, field_ty) in bindings.iter().zip(field_types.iter()) {
            let resolved = self.apply_subst(field_ty);
            self.bind_local(binding_name.clone(), mono(resolved));
        }

        Ok(())
    }

    fn infer_vec_lit(
        &mut self,
        elements: &[Expr],
        span: Span,
    ) -> Result<Type, CranelispError> {
        let elem_type = if elements.is_empty() {
            // Empty vec: polymorphic (Vec fresh_var)
            self.fresh_var()
        } else {
            // Non-empty vec: infer first element, unify all others with it
            let first_ty = self.infer_expr(&elements[0])?;
            for elem in &elements[1..] {
                let elem_ty = self.infer_expr(elem)?;
                self.unify(&first_ty, &elem_ty, elem.span())?;
            }
            self.apply_subst(&first_ty)
        };

        let vec_type = Type::ADT("Vec".into(), vec![elem_type]);
        self.record_expr_type(span, vec_type.clone());
        Ok(vec_type)
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

    // --- String literal tests (Ring 1) ---

    #[test]
    fn test_infer_string_lit() {
        let mut tc = tc();
        let expr = Expr::StringLit {
            value: "hello".to_string(),
            span: span(0, 7),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::String);
    }

    #[test]
    fn test_string_lit_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 7);
        let expr = Expr::StringLit {
            value: "hello".to_string(),
            span: s,
        };
        tc.infer_expr(&expr).unwrap();
        assert_eq!(tc.expr_types.get(&s), Some(&Type::String));
    }

    // --- Data constructor pattern tests (Ring 1) ---

    /// Register (Option a) with None and Some[:a val].
    fn register_option(tc: &mut TypeChecker) {
        tc.register_type_def(
            &TypeName::from("Option"),
            &None,
            &[Symbol::from("a")],
            &[
                ConstructorDef {
                    name: Symbol::from("None"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                ConstructorDef {
                    name: Symbol::from("Some"),
                    docstring: None,
                    fields: vec![cranelisp_types::FieldDef {
                        name: Symbol::from("val"),
                        type_expr: TypeExpr::TypeVar(Symbol::from("a")),
                    }],
                    span: Span::SYNTHETIC,
                },
            ],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();
    }

    #[test]
    fn test_infer_match_data_constructor_pattern() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 42) [(Some x) x (None 0)])
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(8, 12),
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(13, 15),
                }],
                span: span(7, 16),
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Some"),
                        bindings: vec![Symbol::from("x")],
                        span: span(18, 24),
                    },
                    body: Expr::Var {
                        name: Symbol::from("x"),
                        span: span(26, 27),
                    },
                    span: span(18, 27),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("None"),
                        bindings: vec![],
                        span: span(29, 33),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: span(34, 35),
                    },
                    span: span(29, 35),
                },
            ],
            span: span(0, 36),
            compiler_generated: false,
        };

        // Should infer result type Int (x : Int from Some pattern, 0 : Int)
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_match_data_constructor_wrong_binding_count() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 42) [(Some x y) x]) -- too many bindings
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(108, 112),
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(113, 115),
                }],
                span: span(107, 116),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("Some"),
                    bindings: vec![Symbol::from("x"), Symbol::from("y")],
                    span: span(118, 128),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(130, 131),
                },
                span: span(118, 131),
            }],
            span: span(100, 132),
            compiler_generated: false,
        };

        let err = tc.infer_expr(&expr).unwrap_err();
        assert!(err.message().contains("expects 1 field"));
    }

    #[test]
    fn test_infer_match_nullary_with_bindings_errors() {
        let mut tc = tc();
        register_option(&mut tc);

        // (match (Some 1) [(None x) x]) -- None is nullary, no bindings allowed
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(208, 212),
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: span(213, 214),
                }],
                span: span(207, 215),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("None"),
                    bindings: vec![Symbol::from("x")],
                    span: span(217, 224),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(226, 227),
                },
                span: span(217, 227),
            }],
            span: span(200, 228),
            compiler_generated: false,
        };

        let err = tc.infer_expr(&expr).unwrap_err();
        assert!(err.message().contains("takes no arguments"));
    }

    #[test]
    fn test_infer_match_option_non_exhaustive() {
        let mut tc = tc();
        register_option(&mut tc);

        // Match only Some, missing None
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(308, 312),
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: span(313, 314),
                }],
                span: span(307, 315),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("Some"),
                    bindings: vec![Symbol::from("x")],
                    span: span(317, 324),
                },
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: span(326, 327),
                },
                span: span(317, 327),
            }],
            span: span(300, 328),
            compiler_generated: false,
        };

        let err = tc.infer_expr(&expr).unwrap_err();
        assert!(err.message().contains("None"));
    }

    // --- Lambda expr_types completeness (Ring 1 validation) ---

    #[test]
    fn test_lambda_expr_types_recorded() {
        let mut tc = tc();
        let s = span(0, 10);
        let expr = Expr::Lambda {
            params: vec![Symbol::from("x")],
            param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
            body: Box::new(Expr::Var {
                name: Symbol::from("x"),
                span: span(13, 14),
            }),
            span: s,
        };
        tc.infer_expr(&expr).unwrap();

        // Lambda should record a Fn type in expr_types
        let recorded = tc.expr_types.get(&s).unwrap();
        assert!(matches!(recorded, Type::Fn(_, _)));
    }

    // --- Annotate with Applied type (Ring 1) ---

    #[test]
    fn test_annotate_with_applied_type() {
        let mut tc = tc();
        register_option(&mut tc);

        // :(Option Int) (Some 42) -- annotate with applied type
        let annotate_expr = Expr::Annotate {
            annotation: TypeExpr::Applied(
                TypeName::from("Option"),
                vec![TypeExpr::Named(TypeName::from("Int"))],
            ),
            expr: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Some"),
                    span: span(418, 422),
                }),
                args: vec![Expr::IntLit {
                    value: 42,
                    span: span(423, 425),
                }],
                span: span(417, 426),
            }),
            span: span(400, 427),
        };

        let ty = tc.infer_expr(&annotate_expr).unwrap();
        assert_eq!(
            ty,
            Type::ADT(TypeName::from("Option"), vec![Type::Int])
        );
    }

    // --- Product type match tests ---

    #[test]
    fn test_infer_match_product_type() {
        let mut tc = tc();
        // (deftype Point [:Int x :Int y])
        tc.register_type_def(
            &TypeName::from("Point"),
            &None,
            &[],
            &[ConstructorDef {
                name: Symbol::from("Point"),
                docstring: None,
                fields: vec![
                    cranelisp_types::FieldDef {
                        name: Symbol::from("x"),
                        type_expr: TypeExpr::Named(TypeName::from("Int")),
                    },
                    cranelisp_types::FieldDef {
                        name: Symbol::from("y"),
                        type_expr: TypeExpr::Named(TypeName::from("Int")),
                    },
                ],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        )
        .unwrap();

        // (match (Point 1 2) [(Point a b) (add-i64 a b)])
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("Point"),
                    span: span(508, 513),
                }),
                args: vec![
                    Expr::IntLit {
                        value: 1,
                        span: span(514, 515),
                    },
                    Expr::IntLit {
                        value: 2,
                        span: span(516, 517),
                    },
                ],
                span: span(507, 518),
            }),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: Symbol::from("Point"),
                    bindings: vec![Symbol::from("a"), Symbol::from("b")],
                    span: span(520, 530),
                },
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(532, 539),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("a"),
                            span: span(540, 541),
                        },
                        Expr::Var {
                            name: Symbol::from("b"),
                            span: span(542, 543),
                        },
                    ],
                    span: span(531, 544),
                },
                span: span(520, 544),
            }],
            span: span(500, 545),
            compiler_generated: false,
        };

        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_constructor_as_function() {
        let mut tc = tc();
        register_option(&mut tc);

        // (Some 42) -- constructor applied to argument
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: span(601, 605),
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: span(606, 608),
            }],
            span: span(600, 609),
        };

        let ty = tc.infer_expr(&expr).unwrap();
        assert_eq!(
            ty,
            Type::ADT(TypeName::from("Option"), vec![Type::Int])
        );
    }

    #[test]
    fn test_infer_none_has_polymorphic_type() {
        let mut tc = tc();
        register_option(&mut tc);

        // None on its own should be (Option tN) for some N
        let expr = Expr::Var {
            name: Symbol::from("None"),
            span: span(700, 704),
        };

        let ty = tc.infer_expr(&expr).unwrap();
        match &ty {
            Type::ADT(name, args) => {
                assert_eq!(name.as_ref(), "Option");
                assert_eq!(args.len(), 1);
                // The arg should be a fresh var
                assert!(matches!(args[0], Type::Var(_)));
            }
            _ => panic!("None should have ADT type, got {ty:?}"),
        }
    }

    #[test]
    fn test_infer_string_in_if_branches() {
        let mut tc = tc();
        // (if true "hello" "world")
        let expr = Expr::If {
            cond: Box::new(Expr::BoolLit {
                value: true,
                span: span(804, 808),
            }),
            then_branch: Box::new(Expr::StringLit {
                value: "hello".to_string(),
                span: span(809, 816),
            }),
            else_branch: Box::new(Expr::StringLit {
                value: "world".to_string(),
                span: span(817, 824),
            }),
            span: span(800, 825),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::String);
    }

    #[test]
    fn test_infer_string_in_let() {
        let mut tc = tc();
        // (let [s "hello"] s)
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("s"),
                Expr::StringLit {
                    value: "hello".to_string(),
                    span: span(906, 913),
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("s"),
                span: span(915, 916),
            }),
            span: span(900, 917),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::String);
    }

    // --- Vec literal tests (Sprint 3) ---

    #[test]
    fn test_infer_vec_lit_ints() {
        let mut tc = tc();
        // [1 2 3]
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1001, 1002) },
                Expr::IntLit { value: 2, span: span(1003, 1004) },
                Expr::IntLit { value: 3, span: span(1005, 1006) },
            ],
            span: span(1000, 1007),
        };
        assert_eq!(
            tc.infer_expr(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Int])
        );
    }

    #[test]
    fn test_infer_vec_lit_strings() {
        let mut tc = tc();
        // ["a" "b"]
        let expr = Expr::VecLit {
            elements: vec![
                Expr::StringLit { value: "a".into(), span: span(1101, 1104) },
                Expr::StringLit { value: "b".into(), span: span(1105, 1108) },
            ],
            span: span(1100, 1109),
        };
        assert_eq!(
            tc.infer_expr(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::String])
        );
    }

    #[test]
    fn test_infer_vec_lit_empty_is_polymorphic() {
        let mut tc = tc();
        // []
        let expr = Expr::VecLit {
            elements: vec![],
            span: span(1200, 1202),
        };
        let ty = tc.infer_expr(&expr).unwrap();
        match &ty {
            Type::ADT(name, args) => {
                assert_eq!(name.as_ref(), "Vec");
                assert_eq!(args.len(), 1);
                // Element type should be a fresh type variable
                assert!(matches!(args[0], Type::Var(_)));
            }
            _ => panic!("empty vec should be ADT(Vec, [Var]), got {ty:?}"),
        }
    }

    #[test]
    fn test_infer_vec_lit_type_mismatch() {
        let mut tc = tc();
        // [1 "hello"] -- Int vs String
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1301, 1302) },
                Expr::StringLit { value: "hello".into(), span: span(1303, 1310) },
            ],
            span: span(1300, 1311),
        };
        let err = tc.infer_expr(&expr).unwrap_err();
        assert!(err.message().contains("mismatch"), "expected type mismatch error, got: {}", err.message());
    }

    #[test]
    fn test_infer_vec_lit_booleans() {
        let mut tc = tc();
        // [true false]
        let expr = Expr::VecLit {
            elements: vec![
                Expr::BoolLit { value: true, span: span(1401, 1405) },
                Expr::BoolLit { value: false, span: span(1406, 1411) },
            ],
            span: span(1400, 1412),
        };
        assert_eq!(
            tc.infer_expr(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Bool])
        );
    }

    #[test]
    fn test_infer_vec_lit_in_let_binding() {
        let mut tc = tc();
        // (let [xs [1 2 3]] xs)
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("xs"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: span(1508, 1509) },
                        Expr::IntLit { value: 2, span: span(1510, 1511) },
                        Expr::IntLit { value: 3, span: span(1512, 1513) },
                    ],
                    span: span(1507, 1514),
                },
            )],
            body: Box::new(Expr::Var {
                name: Symbol::from("xs"),
                span: span(1516, 1518),
            }),
            span: span(1500, 1519),
        };
        assert_eq!(
            tc.infer_expr(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Int])
        );
    }

    #[test]
    fn test_infer_vec_lit_as_function_arg() {
        let mut tc = tc();
        // Define a function that takes (Vec Int) -> Int
        tc.bind_local(
            Symbol::from("vec-len"),
            mono(Type::Fn(
                vec![Type::ADT(TypeName::from("Vec"), vec![Type::Int])],
                Box::new(Type::Int),
            )),
        );
        // (vec-len [1 2 3])
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: span(1601, 1608),
            }),
            args: vec![Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 1, span: span(1610, 1611) },
                    Expr::IntLit { value: 2, span: span(1612, 1613) },
                    Expr::IntLit { value: 3, span: span(1614, 1615) },
                ],
                span: span(1609, 1616),
            }],
            span: span(1600, 1617),
        };
        assert_eq!(tc.infer_expr(&expr).unwrap(), Type::Int);
    }

    #[test]
    fn test_infer_vec_lit_as_function_return() {
        let mut tc = tc();
        // (fn [x] [x]) -- returns Vec of the param type
        let expr = Expr::Lambda {
            params: vec![Symbol::from("x")],
            param_annotations: vec![Some(TypeExpr::Named(TypeName::from("Int")))],
            body: Box::new(Expr::VecLit {
                elements: vec![Expr::Var {
                    name: Symbol::from("x"),
                    span: span(1710, 1711),
                }],
                span: span(1709, 1712),
            }),
            span: span(1700, 1713),
        };
        let ty = tc.infer_expr(&expr).unwrap();
        assert_eq!(
            ty,
            Type::Fn(
                vec![Type::Int],
                Box::new(Type::ADT(TypeName::from("Vec"), vec![Type::Int]))
            )
        );
    }

    #[test]
    fn test_infer_vec_lit_single_element() {
        let mut tc = tc();
        // [42]
        let expr = Expr::VecLit {
            elements: vec![Expr::IntLit { value: 42, span: span(1801, 1803) }],
            span: span(1800, 1804),
        };
        assert_eq!(
            tc.infer_expr(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Int])
        );
    }

    #[test]
    fn test_infer_vec_lit_expr_type_recorded() {
        let mut tc = tc();
        let s = span(1900, 1907);
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: span(1901, 1902) },
                Expr::IntLit { value: 2, span: span(1903, 1904) },
            ],
            span: s,
        };
        tc.infer_expr(&expr).unwrap();
        assert_eq!(
            tc.expr_types.get(&s),
            Some(&Type::ADT(TypeName::from("Vec"), vec![Type::Int]))
        );
    }

    #[test]
    fn test_infer_vec_lit_floats() {
        let mut tc = tc();
        // [1.0 2.0 3.0]
        let expr = Expr::VecLit {
            elements: vec![
                Expr::FloatLit { value: 1.0, span: span(2001, 2004) },
                Expr::FloatLit { value: 2.0, span: span(2005, 2008) },
                Expr::FloatLit { value: 3.0, span: span(2009, 2012) },
            ],
            span: span(2000, 2013),
        };
        assert_eq!(
            tc.infer_expr(&expr).unwrap(),
            Type::ADT(TypeName::from("Vec"), vec![Type::Float])
        );
    }
}
