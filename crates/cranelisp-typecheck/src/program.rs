//! Two-pass batch checking and REPL input checking.
//!
//! `check_program` orchestrates Pass 1 (registration) and Pass 2 (checking).
//! Each phase is a named private method. Addresses audit HIGH-2.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{
    CheckResult, CranelispError, Defn, DefKind, ModuleEntry,
    ReplCheckResult, ReplInput, Scheme, Span, Symbol, TopLevel, Type,
    apply,
};

use crate::checker::TypeChecker;
use crate::resolve::resolve_type_expr;
use crate::scheme::mono;

impl TypeChecker {
    /// Check a complete program (batch mode).
    ///
    /// Two-pass pipeline:
    /// 1. Register type definitions and function signatures.
    /// 2. Check function bodies, generalize types.
    pub fn check_program(
        &mut self,
        program: &[TopLevel],
    ) -> Result<CheckResult, CranelispError> {
        // Pass 1: register type definitions
        self.register_type_defs_from_program(program)?;

        // Pass 1: register function signatures with fresh type variables
        let defns = Self::collect_defns(program);
        let defn_type_vars = self.pass1_register_signatures(&defns)?;

        // Pass 2: check function bodies and generalize
        self.pass2_check_bodies(&defns, &defn_type_vars)?;

        Ok(self.build_check_result())
    }

    /// Check a single REPL input incrementally.
    pub fn check_repl_input(
        &mut self,
        input: &ReplInput,
    ) -> Result<ReplCheckResult, CranelispError> {
        match input {
            ReplInput::Expr(expr) => {
                let ty = self.infer_expr(expr)?;
                let resolved = self.apply_subst(&ty);
                Ok(self.build_repl_result(resolved, None))
            }

            ReplInput::Defn(defn) => {
                let (ty, scheme) = self.check_single_defn(defn)?;
                Ok(self.build_repl_result(ty, Some(scheme)))
            }

            ReplInput::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } => {
                self.register_type_def(name, docstring, type_params, constructors, *visibility, *span)?;
                let ty = Type::ADT(name.clone(), vec![]);
                Ok(self.build_repl_result(ty, None))
            }

            // Not supported in Ring 0
            ReplInput::DefnMulti { span, .. } => Err(CranelispError::TypeError {
                message: "multi-signature functions not supported in Ring 0".into(),
                span: *span,
            }),
            ReplInput::TraitDecl(decl) => Err(CranelispError::TypeError {
                message: "trait declarations not supported in Ring 0".into(),
                span: decl.span,
            }),
            ReplInput::TraitImpl(impl_) => Err(CranelispError::TypeError {
                message: "trait implementations not supported in Ring 0".into(),
                span: impl_.span,
            }),
        }
    }

    // --- Pass 1: Registration ---

    /// Register all TypeDef entries from the program.
    fn register_type_defs_from_program(
        &mut self,
        program: &[TopLevel],
    ) -> Result<(), CranelispError> {
        for top in program {
            if let TopLevel::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                visibility,
                span,
            } = top
            {
                self.register_type_def(
                    name,
                    docstring,
                    type_params,
                    constructors,
                    *visibility,
                    *span,
                )?;
            }
        }
        Ok(())
    }

    /// Collect all Defn entries from the program.
    fn collect_defns(program: &[TopLevel]) -> Vec<&Defn> {
        program
            .iter()
            .filter_map(|top| {
                if let TopLevel::Defn(defn) = top {
                    Some(defn)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Create fresh type variables for a function's parameters and return type,
    /// respecting any annotations, and register the signature in the symbol table.
    ///
    /// Returns `(param_types, return_type)` for use in body checking.
    /// Shared by `pass1_register_signatures` (batch) and `check_single_defn` (REPL)
    /// to prevent the two paths from diverging as rings add complexity.
    fn register_defn_signature(
        &mut self,
        defn: &Defn,
    ) -> Result<(Vec<Type>, Type), CranelispError> {
        let mut param_types = Vec::new();
        for (i, _param) in defn.params.iter().enumerate() {
            let param_ty = if let Some(Some(ann)) = defn.param_annotations.get(i) {
                let known = self.known_type_names();
                let var_map = HashMap::new();
                resolve_type_expr(ann, &var_map, &known, defn.span)?
            } else {
                self.fresh_var()
            };
            param_types.push(param_ty);
        }
        let ret_ty = self.fresh_var();

        let fn_type = Type::Fn(param_types.clone(), Box::new(ret_ty.clone()));
        let scheme = mono(fn_type);

        self.symbol_table.insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme,
                visibility: defn.visibility,
                docstring: defn.docstring.clone(),
                param_names: defn.params.clone(),
                kind: Box::new(DefKind::UserFn {
                    constrained_fn: None,
                }),
            },
        );

        Ok((param_types, ret_ty))
    }

    /// Pass 1: Register function signatures with fresh type variables.
    ///
    /// Returns a map from function name to (param type vars, return type var)
    /// for use in Pass 2.
    fn pass1_register_signatures(
        &mut self,
        defns: &[&Defn],
    ) -> Result<HashMap<Symbol, (Vec<Type>, Type)>, CranelispError> {
        let mut type_vars = HashMap::new();

        for defn in defns {
            let (param_types, ret_ty) = self.register_defn_signature(defn)?;
            type_vars.insert(defn.name.clone(), (param_types, ret_ty));
        }

        Ok(type_vars)
    }

    /// Pass 2: Check function bodies and generalize types.
    fn pass2_check_bodies(
        &mut self,
        defns: &[&Defn],
        type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Result<(), CranelispError> {
        for defn in defns {
            let (param_types, ret_ty) = type_vars
                .get(&defn.name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("internal: missing type vars for {}", defn.name),
                    span: defn.span,
                })?;

            self.check_defn_body(defn, param_types, ret_ty)?;
        }

        // After all bodies are checked, generalize each function's type
        for defn in defns {
            let (param_types, ret_ty) = type_vars
                .get(&defn.name)
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("internal: missing type vars for {}", defn.name),
                    span: defn.span,
                })?;

            let fn_type = Type::Fn(
                param_types.iter().map(|t| self.apply_subst(t)).collect(),
                Box::new(self.apply_subst(ret_ty)),
            );
            let scheme = self.generalize(&fn_type);

            // Update the symbol table entry with the generalized scheme
            if let Some(ModuleEntry::Def { scheme: s, .. }) =
                self.symbol_table.symbols.get_mut(&defn.name)
            {
                *s = scheme;
            }
        }

        Ok(())
    }

    /// Check a single function definition body.
    fn check_defn_body(
        &mut self,
        defn: &Defn,
        param_types: &[Type],
        ret_ty: &Type,
    ) -> Result<(), CranelispError> {
        self.push_scope();

        // Bind parameters
        for (param_name, param_ty) in defn.params.iter().zip(param_types.iter()) {
            self.bind_local(param_name.clone(), mono(param_ty.clone()));
        }

        // Bind the function name for recursion
        let fn_type = Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone()));
        self.bind_local(defn.name.clone(), mono(fn_type));

        // Infer body type
        let body_ty = self.infer_expr(&defn.body)?;

        // Unify body type with return type variable
        self.unify(&body_ty, ret_ty, defn.span)?;

        self.pop_scope();
        Ok(())
    }

    /// Check a single defn for REPL (register, check, generalize in one step).
    fn check_single_defn(
        &mut self,
        defn: &Defn,
    ) -> Result<(Type, Scheme), CranelispError> {
        let (param_types, ret_ty) = self.register_defn_signature(defn)?;

        // Check body
        self.check_defn_body(defn, &param_types, &ret_ty)?;

        // Generalize
        let resolved_fn_type = Type::Fn(
            param_types.iter().map(|t| self.apply_subst(t)).collect(),
            Box::new(self.apply_subst(&ret_ty)),
        );
        let scheme = self.generalize(&resolved_fn_type);

        // Update symbol table with generalized scheme
        if let Some(ModuleEntry::Def { scheme: s, .. }) =
            self.symbol_table.symbols.get_mut(&defn.name)
        {
            *s = scheme.clone();
        }

        Ok((scheme.ty.clone(), scheme))
    }

    // --- Result building ---

    /// Resolve all recorded expr_types through the current substitution.
    fn resolve_expr_types(&self) -> HashMap<Span, Type> {
        self.expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&self.subst, ty)))
            .collect()
    }

    /// Build the final CheckResult from accumulated state.
    fn build_check_result(&mut self) -> CheckResult {
        let resolved_expr_types = self.resolve_expr_types();

        CheckResult {
            method_resolutions: std::mem::take(&mut self.method_resolutions),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: resolved_expr_types,
            default_method_defns: Vec::new(),
            warnings: std::mem::take(&mut self.warnings),
            type_defs: self.type_defs.type_defs.clone(),
            constructor_to_type: self.type_defs.constructor_to_type.clone(),
        }
    }

    /// Build a ReplCheckResult from the current state.
    fn build_repl_result(&mut self, ty: Type, scheme: Option<Scheme>) -> ReplCheckResult {
        let resolved_expr_types = self.resolve_expr_types();

        ReplCheckResult {
            ty,
            scheme,
            method_resolutions: std::mem::take(&mut self.method_resolutions),
            expr_types: resolved_expr_types,
            warnings: std::mem::take(&mut self.warnings),
            type_defs: self.type_defs.type_defs.clone(),
            constructor_to_type: self.type_defs.constructor_to_type.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{Expr, ReplInput, TypeName, Visibility};

    fn span(start: u32, end: u32) -> Span {
        Span::new(start, end)
    }

    #[test]
    fn test_check_program_simple_defn() {
        let mut tc = TypeChecker::new();
        // (defn add-one [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("add-one"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(20, 27),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(28, 29),
                    },
                    Expr::IntLit {
                        value: 1,
                        span: span(30, 31),
                    },
                ],
                span: span(19, 32),
            },
            visibility: Visibility::Public,
            span: span(0, 33),
        })];

        let _result = tc.check_program(&program).unwrap();

        // Check the function was registered with correct type: Fn([Int], Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("add-one") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add-one not found in symbol table");
        }
    }

    #[test]
    fn test_check_program_identity_is_polymorphic() {
        let mut tc = TypeChecker::new();
        // (defn id [x] x)
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Var {
                name: Symbol::from("x"),
                span: span(14, 15),
            },
            visibility: Visibility::Public,
            span: span(0, 16),
        })];

        tc.check_program(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("id") {
            // Should be forall [a]. Fn([a], a)
            assert_eq!(scheme.vars.len(), 1, "id should have 1 quantified var");
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert_eq!(params[0], **ret);
                }
                _ => panic!("expected Fn type"),
            }
        } else {
            panic!("id not found in symbol table");
        }
    }

    #[test]
    fn test_check_program_recursive_function() {
        let mut tc = TypeChecker::new();
        // (defn fact [n] (if (eq-i64 n 0) 1 (mul-i64 n (fact (sub-i64 n 1)))))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("fact"),
            docstring: None,
            params: vec![Symbol::from("n")],
            param_annotations: vec![None],
            body: Expr::If {
                cond: Box::new(Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("eq-i64"),
                        span: span(20, 26),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("n"),
                            span: span(27, 28),
                        },
                        Expr::IntLit {
                            value: 0,
                            span: span(29, 30),
                        },
                    ],
                    span: span(19, 31),
                }),
                then_branch: Box::new(Expr::IntLit {
                    value: 1,
                    span: span(33, 34),
                }),
                else_branch: Box::new(Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("mul-i64"),
                        span: span(36, 43),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("n"),
                            span: span(44, 45),
                        },
                        Expr::Apply {
                            callee: Box::new(Expr::Var {
                                name: Symbol::from("fact"),
                                span: span(47, 51),
                            }),
                            args: vec![Expr::Apply {
                                callee: Box::new(Expr::Var {
                                    name: Symbol::from("sub-i64"),
                                    span: span(53, 60),
                                }),
                                args: vec![
                                    Expr::Var {
                                        name: Symbol::from("n"),
                                        span: span(61, 62),
                                    },
                                    Expr::IntLit {
                                        value: 1,
                                        span: span(63, 64),
                                    },
                                ],
                                span: span(52, 65),
                            }],
                            span: span(46, 66),
                        },
                    ],
                    span: span(35, 67),
                }),
                span: span(15, 68),
            },
            visibility: Visibility::Public,
            span: span(0, 69),
        })];

        tc.check_program(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("fact") {
            assert!(
                scheme.vars.is_empty(),
                "fact should be monomorphic (Int -> Int)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("fact not found in symbol table");
        }
    }

    #[test]
    fn test_check_program_with_typedef() {
        let mut tc = TypeChecker::new();
        let program = vec![
            TopLevel::TypeDef {
                name: TypeName::from("Color"),
                docstring: None,
                type_params: vec![],
                constructors: vec![
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Red"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                    cranelisp_types::ConstructorDef {
                        name: Symbol::from("Green"),
                        docstring: None,
                        fields: vec![],
                        span: Span::SYNTHETIC,
                    },
                ],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            },
            TopLevel::Defn(Defn {
                name: Symbol::from("is-red"),
                docstring: None,
                params: vec![Symbol::from("c")],
                param_annotations: vec![None],
                body: Expr::Match {
                    scrutinee: Box::new(Expr::Var {
                        name: Symbol::from("c"),
                        span: span(30, 31),
                    }),
                    arms: vec![
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Constructor {
                                name: Symbol::from("Red"),
                                bindings: vec![],
                                span: span(33, 36),
                            },
                            body: Expr::BoolLit {
                                value: true,
                                span: span(37, 41),
                            },
                            span: span(33, 41),
                        },
                        cranelisp_types::MatchArm {
                            pattern: cranelisp_types::Pattern::Wildcard {
                                span: span(42, 43),
                            },
                            body: Expr::BoolLit {
                                value: false,
                                span: span(44, 49),
                            },
                            span: span(42, 49),
                        },
                    ],
                    span: span(24, 50),
                    compiler_generated: false,
                },
                visibility: Visibility::Public,
                span: span(0, 51),
            }),
        ];

        let result = tc.check_program(&program).unwrap();

        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("is-red") {
            assert_eq!(
                scheme.ty,
                Type::Fn(
                    vec![Type::ADT(TypeName::from("Color"), vec![])],
                    Box::new(Type::Bool)
                )
            );
        } else {
            panic!("is-red not found in symbol table");
        }

        // Type defs should be in the result
        assert!(result.type_defs.contains_key(&TypeName::from("Color")));
        assert!(result.constructor_to_type.contains_key("Red"));
    }

    #[test]
    fn test_check_program_type_error() {
        let mut tc = TypeChecker::new();
        // (defn bad [x] (add-i64 x true)) -- type error: Bool arg to monomorphic Int primitive
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("bad"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(16, 23),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(24, 25),
                    },
                    Expr::BoolLit {
                        value: true,
                        span: span(26, 30),
                    },
                ],
                span: span(15, 31),
            },
            visibility: Visibility::Public,
            span: span(0, 32),
        })];

        // add-i64 has monomorphic type (Fn [Int Int] Int) so (add-i64 x true) is a
        // type error: Bool cannot unify with Int.
        let result = tc.check_program(&program);
        assert!(result.is_err());
    }

    #[test]
    fn test_check_program_expr_types_resolved() {
        let mut tc = TypeChecker::new();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(16, 23),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(24, 25),
                    },
                    Expr::IntLit {
                        value: 1,
                        span: span(26, 27),
                    },
                ],
                span: span(15, 28),
            },
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let result = tc.check_program(&program).unwrap();

        // All expr_types should be resolved (no Var types)
        for (span, ty) in &result.expr_types {
            if let Type::Var(_) = ty {
                panic!("unresolved Var in expr_types at {span}");
            }
        }
    }

    #[test]
    fn test_check_repl_expression() {
        let mut tc = TypeChecker::new();
        let input = ReplInput::Expr(Expr::IntLit {
            value: 42,
            span: span(0, 2),
        });
        let result = tc.check_repl_input(&input).unwrap();
        assert_eq!(result.ty, Type::Int);
        assert!(result.scheme.is_none());
    }

    #[test]
    fn test_check_repl_defn() {
        let mut tc = TypeChecker::new();
        let input = ReplInput::Defn(Defn {
            name: Symbol::from("id"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Var {
                name: Symbol::from("x"),
                span: span(14, 15),
            },
            visibility: Visibility::Public,
            span: span(0, 16),
        });
        let result = tc.check_repl_input(&input).unwrap();

        // The scheme should be polymorphic
        let scheme = result.scheme.unwrap();
        assert_eq!(scheme.vars.len(), 1);
    }

    #[test]
    fn test_check_repl_typedef() {
        let mut tc = TypeChecker::new();
        let input = ReplInput::TypeDef {
            name: TypeName::from("Dir"),
            docstring: None,
            type_params: vec![],
            constructors: vec![
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("North"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
                cranelisp_types::ConstructorDef {
                    name: Symbol::from("South"),
                    docstring: None,
                    fields: vec![],
                    span: Span::SYNTHETIC,
                },
            ],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let result = tc.check_repl_input(&input).unwrap();
        assert_eq!(result.ty, Type::ADT(TypeName::from("Dir"), vec![]));
        assert!(result.type_defs.contains_key(&TypeName::from("Dir")));
    }

    #[test]
    fn test_check_program_forward_reference() {
        let mut tc = TypeChecker::new();
        // Two functions where the first calls the second
        // (defn double [x] (add-self x))
        // (defn add-self [y] (add-i64 y y))
        //
        // add-i64 is monomorphic (Fn [Int Int] Int), so add-self is pinned to Int.
        // double's type unifies with add-self's type through the call.
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                params: vec![Symbol::from("x")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-self"),
                        span: span(18, 26),
                    }),
                    args: vec![Expr::Var {
                        name: Symbol::from("x"),
                        span: span(27, 28),
                    }],
                    span: span(17, 29),
                },
                visibility: Visibility::Public,
                span: span(0, 30),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                params: vec![Symbol::from("y")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(48, 55),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("y"),
                            span: span(56, 57),
                        },
                        Expr::Var {
                            name: Symbol::from("y"),
                            span: span(58, 59),
                        },
                    ],
                    span: span(47, 60),
                },
                visibility: Visibility::Public,
                span: span(31, 61),
            }),
        ];

        tc.check_program(&program).unwrap();

        // add-self is monomorphic: Fn([Int], Int) — add-i64 pins y to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("add-self") {
            assert!(
                scheme.vars.is_empty(),
                "add-self should have no quantified vars (monomorphic via add-i64)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "add-self: (Fn [Int] Int)"
            );
        } else {
            panic!("add-self not found in symbol table");
        }

        // double should also be monomorphic (calls add-self with Int)
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("double") {
            assert!(
                scheme.vars.is_empty(),
                "double should have no quantified vars (monomorphic via add-self)"
            );
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                "double: (Fn [Int] Int)"
            );
        } else {
            panic!("double not found in symbol table");
        }
    }

    #[test]
    fn test_check_program_forward_reference_pinned() {
        let mut tc = TypeChecker::new();
        // (defn double [:Int x] (add-self x))
        // (defn add-self [y] (add-i64 y y))
        // Both are monomorphic: add-i64 pins y to Int, and annotation pins x to Int.
        let program = vec![
            TopLevel::Defn(Defn {
                name: Symbol::from("double"),
                docstring: None,
                params: vec![Symbol::from("x")],
                param_annotations: vec![Some(cranelisp_types::TypeExpr::Named(TypeName::from("Int")))],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-self"),
                        span: span(118, 126),
                    }),
                    args: vec![Expr::Var {
                        name: Symbol::from("x"),
                        span: span(127, 128),
                    }],
                    span: span(117, 129),
                },
                visibility: Visibility::Public,
                span: span(100, 130),
            }),
            TopLevel::Defn(Defn {
                name: Symbol::from("add-self"),
                docstring: None,
                params: vec![Symbol::from("y")],
                param_annotations: vec![None],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("add-i64"),
                        span: span(148, 155),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("y"),
                            span: span(156, 157),
                        },
                        Expr::Var {
                            name: Symbol::from("y"),
                            span: span(158, 159),
                        },
                    ],
                    span: span(147, 160),
                },
                visibility: Visibility::Public,
                span: span(131, 161),
            }),
        ];

        tc.check_program(&program).unwrap();

        // double is pinned: Fn([Int], Int) — annotation + add-i64 both constrain to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("double") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("double not found");
        }

        // add-self is also pinned: Fn([Int], Int) — add-i64 constrains y to Int
        if let Some(ModuleEntry::Def { scheme, .. }) = tc.symbol_table.get("add-self") {
            assert_eq!(
                scheme.ty,
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            );
        } else {
            panic!("add-self not found");
        }
    }

    #[test]
    fn test_check_program_check_result_has_builtin_resolutions() {
        let mut tc = TypeChecker::new();
        // (defn inc [x] (add-i64 x 1))
        let program = vec![TopLevel::Defn(Defn {
            name: Symbol::from("inc"),
            docstring: None,
            params: vec![Symbol::from("x")],
            param_annotations: vec![None],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("add-i64"),
                    span: span(16, 23),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("x"),
                        span: span(24, 25),
                    },
                    Expr::IntLit {
                        value: 1,
                        span: span(26, 27),
                    },
                ],
                span: span(15, 28),
            },
            visibility: Visibility::Public,
            span: span(0, 29),
        })];

        let result = tc.check_program(&program).unwrap();

        // The add-i64 call site should have a BuiltinFn resolution
        assert!(!result.method_resolutions.is_empty());
        let resolution = result.method_resolutions.get(&span(15, 28)).unwrap();
        match resolution {
            cranelisp_types::ResolvedCall::BuiltinFn { name } => {
                assert_eq!(name.as_ref(), "add-i64");
            }
            _ => panic!("expected BuiltinFn"),
        }
    }
}
