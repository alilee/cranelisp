use std::collections::HashSet;

use crate::ast::*;

/// Compute the set of free variables in an expression.
/// `globals` contains names of top-level functions and builtins that should not be captured.
pub fn free_vars(expr: &Expr, globals: &HashSet<String>) -> HashSet<String> {
    match expr {
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. } => HashSet::new(),
        Expr::Var { name, .. } => {
            if globals.contains(name) {
                HashSet::new()
            } else {
                let mut s = HashSet::new();
                s.insert(name.clone());
                s
            }
        }
        Expr::Let { bindings, body, .. } => {
            let mut fv = HashSet::new();
            let mut bound = HashSet::new();
            for (name, val_expr) in bindings {
                // The value expression can reference previously bound names
                let val_fv = free_vars(val_expr, globals);
                for v in val_fv {
                    if !bound.contains(&v) {
                        fv.insert(v);
                    }
                }
                bound.insert(name.clone());
            }
            let body_fv = free_vars(body, globals);
            for v in body_fv {
                if !bound.contains(&v) {
                    fv.insert(v);
                }
            }
            fv
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            let mut fv = free_vars(cond, globals);
            fv.extend(free_vars(then_branch, globals));
            fv.extend(free_vars(else_branch, globals));
            fv
        }
        Expr::Lambda { params, body, .. } => {
            let body_fv = free_vars(body, globals);
            let param_set: HashSet<String> = params.iter().cloned().collect();
            body_fv
                .into_iter()
                .filter(|v| !param_set.contains(v))
                .collect()
        }
        Expr::Apply { callee, args, .. } => {
            let mut fv = free_vars(callee, globals);
            for arg in args {
                fv.extend(free_vars(arg, globals));
            }
            fv
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            let mut fv = free_vars(scrutinee, globals);
            for arm in arms {
                let arm_fv = free_vars(&arm.body, globals);
                let bound: HashSet<String> = match &arm.pattern {
                    Pattern::Constructor { bindings, .. } => bindings.iter().cloned().collect(),
                    Pattern::Var { name, .. } => {
                        let mut s = HashSet::new();
                        s.insert(name.clone());
                        s
                    }
                    Pattern::Wildcard { .. } => HashSet::new(),
                };
                for v in arm_fv {
                    if !bound.contains(&v) {
                        fv.insert(v);
                    }
                }
            }
            fv
        }
        Expr::VecLit { elements, .. } => {
            let mut fv = HashSet::new();
            for elem in elements {
                fv.extend(free_vars(elem, globals));
            }
            fv
        }
        Expr::Annotate { expr, .. } => free_vars(expr, globals),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast_builder::parse_expr;

    fn fv(src: &str) -> HashSet<String> {
        let expr = parse_expr(src).unwrap();
        free_vars(&expr, &HashSet::new())
    }

    fn fv_with_globals(src: &str, globals: &[&str]) -> HashSet<String> {
        let expr = parse_expr(src).unwrap();
        let g: HashSet<String> = globals.iter().map(|s| s.to_string()).collect();
        free_vars(&expr, &g)
    }

    #[test]
    fn literal_has_no_free_vars() {
        assert!(fv("42").is_empty());
        assert!(fv("true").is_empty());
    }

    #[test]
    fn var_is_free() {
        assert_eq!(fv("x"), ["x".to_string()].into());
    }

    #[test]
    fn global_not_free() {
        assert!(fv_with_globals("print", &["print"]).is_empty());
    }

    #[test]
    fn lambda_binds_params() {
        assert!(fv("(fn [x] x)").is_empty());
    }

    #[test]
    fn lambda_with_capture() {
        // + is now a Var, so pass operators as globals (matching real codegen usage)
        assert_eq!(
            fv_with_globals("(fn [x] (+ x n))", &["+"]),
            ["n".to_string()].into()
        );
    }

    #[test]
    fn let_binds_vars() {
        assert!(fv("(let [x 1] x)").is_empty());
    }

    #[test]
    fn do_free_vars() {
        // do is now a macro/function — parses as Apply, captures do + args
        let fvs = fv("(do x y)");
        assert!(fvs.contains("do"));
        assert!(fvs.contains("x"));
        assert!(fvs.contains("y"));
    }

    #[test]
    fn pure_free_vars() {
        // pure is now a function — parses as Apply, captures pure + x
        let fvs = fv("(pure x)");
        assert!(fvs.contains("pure"));
        assert!(fvs.contains("x"));
    }

    #[test]
    fn bind_free_vars() {
        // bind is now a function — parses as Apply, captures bind + args
        let fvs = fv("(bind x (fn [a] y))");
        assert!(fvs.contains("bind"));
        assert!(fvs.contains("x"));
        assert!(fvs.contains("y"));
        assert!(!fvs.contains("a"));
    }

    #[test]
    fn nested_capture() {
        let fvs = fv_with_globals("(fn [x] (fn [y] (+ x (+ y z))))", &["+"]);
        assert_eq!(fvs, ["z".to_string()].into());
    }

    #[test]
    fn annotate_free_vars() {
        let fvs = fv(":Int x");
        assert_eq!(fvs, ["x".to_string()].into());
    }

    #[test]
    fn annotate_literal_no_free_vars() {
        assert!(fv(":Int 42").is_empty());
    }
}
