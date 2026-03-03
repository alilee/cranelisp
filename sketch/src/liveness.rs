//! Liveness analysis: compute which Var references are "last use" of their binding.
//!
//! A Var is last-use when no subsequent expression in the same evaluation order
//! references the same binding. The caller uses this to decide whether to transfer
//! ownership (no inc needed) or borrow (inc needed) when passing args.

use std::collections::HashSet;

use crate::ast::*;
use crate::captures::free_vars;
use crate::error::Span;

/// Compute the set of Var spans that are the last use of their binding.
///
/// `globals` is the set of top-level/builtin names (these are never consumed).
/// Returns a `HashSet<Span>` — each entry is a Var expression whose span is in
/// the set, meaning that Var is the last reference to its binding in evaluation order.
pub fn compute_last_uses(body: &Expr, globals: &HashSet<String>) -> HashSet<Span> {
    let mut result = HashSet::new();
    let used_after = HashSet::new();
    walk_expr(body, &used_after, globals, &mut result);
    result
}

/// Recursive walk: `used_after` contains variable names that are used in expressions
/// evaluated after this one (in the enclosing context). A Var is last-use when its
/// name is NOT in `used_after`.
fn walk_expr(
    expr: &Expr,
    used_after: &HashSet<String>,
    globals: &HashSet<String>,
    result: &mut HashSet<Span>,
) {
    match expr {
        Expr::IntLit { .. }
        | Expr::FloatLit { .. }
        | Expr::BoolLit { .. }
        | Expr::StringLit { .. } => {}

        Expr::Var { name, span, .. } => {
            // Global names and dotted names are never consumed
            if globals.contains(name) || name.contains('.') {
                return;
            }
            if !used_after.contains(name) {
                result.insert(*span);
            }
        }

        Expr::Let { bindings, body, .. } => {
            // bindings evaluated left-to-right, then body
            // binding[i]'s used_after = free_vars(binding[i+1..]) ∪ free_vars(body) ∪ outer used_after
            let body_fv = free_vars(body, globals);
            for i in 0..bindings.len() {
                let mut ua = used_after.clone();
                ua.extend(body_fv.iter().cloned());
                // Add free vars from all subsequent bindings
                for j in (i + 1)..bindings.len() {
                    ua.extend(free_vars(&bindings[j].1, globals));
                }
                // The binding name itself is introduced after this expr,
                // so remove it from used_after for the value expression
                ua.remove(&bindings[i].0);
                walk_expr(&bindings[i].1, &ua, globals, result);
            }
            // Body's used_after is the outer used_after
            walk_expr(body, used_after, globals, result);
        }

        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            // Condition's used_after includes both branches + outer
            let then_fv = free_vars(then_branch, globals);
            let else_fv = free_vars(else_branch, globals);
            let mut cond_ua = used_after.clone();
            cond_ua.extend(then_fv);
            cond_ua.extend(else_fv);
            walk_expr(cond, &cond_ua, globals, result);

            // Each branch: conservative — treat as if both branches execute
            // (i.e. used_after = outer used_after, no cross-branch consumption)
            walk_expr(then_branch, used_after, globals, result);
            walk_expr(else_branch, used_after, globals, result);
        }

        Expr::Lambda { body, .. } => {
            // Lambda body is a separate function — analyzed independently
            let inner_last = compute_last_uses(body, globals);
            result.extend(inner_last);
        }

        Expr::Apply { callee, args, .. } => {
            // Callee + args evaluated left-to-right
            // callee's used_after = free_vars(args) ∪ outer used_after
            let mut callee_ua = used_after.clone();
            for arg in args {
                callee_ua.extend(free_vars(arg, globals));
            }
            walk_expr(callee, &callee_ua, globals, result);

            // arg[i]'s used_after = free_vars(arg[i+1..]) ∪ outer used_after
            for i in 0..args.len() {
                let mut ua = used_after.clone();
                for j in (i + 1)..args.len() {
                    ua.extend(free_vars(&args[j], globals));
                }
                walk_expr(&args[i], &ua, globals, result);
            }
        }

        Expr::Match {
            scrutinee, arms, ..
        } => {
            // Scrutinee's used_after includes all arm bodies + outer
            let mut scrut_ua = used_after.clone();
            for arm in arms {
                scrut_ua.extend(free_vars(&arm.body, globals));
            }
            walk_expr(scrutinee, &scrut_ua, globals, result);

            // Each arm body: conservative (same as If branches)
            for arm in arms {
                walk_expr(&arm.body, used_after, globals, result);
            }
        }

        Expr::VecLit { elements, .. } => {
            // Elements evaluated left-to-right
            for i in 0..elements.len() {
                let mut ua = used_after.clone();
                for j in (i + 1)..elements.len() {
                    ua.extend(free_vars(&elements[j], globals));
                }
                walk_expr(&elements[i], &ua, globals, result);
            }
        }

        Expr::Annotate { expr: inner, .. } => {
            walk_expr(inner, used_after, globals, result);
        }

        Expr::ParLet { bindings, body, .. } => {
            // Par-let bindings are independent (no ordering between them)
            // so each binding's used_after = free_vars(body) ∪ outer used_after
            // (but NOT other bindings, since they evaluate in parallel)
            let body_fv = free_vars(body, globals);
            let mut binding_ua = used_after.clone();
            binding_ua.extend(body_fv);
            for (_, val_expr) in bindings {
                walk_expr(val_expr, &binding_ua, globals, result);
            }
            walk_expr(body, used_after, globals, result);
        }

        Expr::ParBind { bindings, body, .. } => {
            // Same as ParLet: bindings are independent
            let body_fv = free_vars(body, globals);
            let mut binding_ua = used_after.clone();
            binding_ua.extend(body_fv);
            for (_, val_expr) in bindings {
                walk_expr(val_expr, &binding_ua, globals, result);
            }
            walk_expr(body, used_after, globals, result);
        }

        Expr::Trace { body, .. } => {
            // Treat like a simple expression: free vars in body are live
            walk_expr(body, used_after, globals, result);
        }
        Expr::RunTests { init, pass_fn, fail_fn, .. } => {
            walk_expr(init, used_after, globals, result);
            walk_expr(pass_fn, used_after, globals, result);
            walk_expr(fail_fn, used_after, globals, result);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast_builder::parse_expr;

    fn last_use_names(src: &str) -> Vec<String> {
        let expr = parse_expr(src).unwrap();
        let globals = HashSet::new();
        let last_uses = compute_last_uses(&expr, &globals);
        // Collect the names of Var exprs that are last-use
        let mut names = Vec::new();
        collect_last_use_var_names(&expr, &last_uses, &mut names);
        names.sort();
        names
    }

    fn last_use_names_with_globals(src: &str, globs: &[&str]) -> Vec<String> {
        let expr = parse_expr(src).unwrap();
        let globals: HashSet<String> = globs.iter().map(|s| s.to_string()).collect();
        let last_uses = compute_last_uses(&expr, &globals);
        let mut names = Vec::new();
        collect_last_use_var_names(&expr, &last_uses, &mut names);
        names.sort();
        names
    }

    fn collect_last_use_var_names(expr: &Expr, last_uses: &HashSet<Span>, out: &mut Vec<String>) {
        match expr {
            Expr::Var { name, span, .. } => {
                if last_uses.contains(span) {
                    out.push(name.clone());
                }
            }
            Expr::Let { bindings, body, .. } => {
                for (_, val) in bindings {
                    collect_last_use_var_names(val, last_uses, out);
                }
                collect_last_use_var_names(body, last_uses, out);
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                collect_last_use_var_names(cond, last_uses, out);
                collect_last_use_var_names(then_branch, last_uses, out);
                collect_last_use_var_names(else_branch, last_uses, out);
            }
            Expr::Apply { callee, args, .. } => {
                collect_last_use_var_names(callee, last_uses, out);
                for arg in args {
                    collect_last_use_var_names(arg, last_uses, out);
                }
            }
            Expr::Lambda { body, .. } => {
                collect_last_use_var_names(body, last_uses, out);
            }
            Expr::Match {
                scrutinee, arms, ..
            } => {
                collect_last_use_var_names(scrutinee, last_uses, out);
                for arm in arms {
                    collect_last_use_var_names(&arm.body, last_uses, out);
                }
            }
            Expr::VecLit { elements, .. } => {
                for e in elements {
                    collect_last_use_var_names(e, last_uses, out);
                }
            }
            Expr::Annotate { expr, .. } => {
                collect_last_use_var_names(expr, last_uses, out);
            }
            Expr::ParLet { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                for (_, val) in bindings {
                    collect_last_use_var_names(val, last_uses, out);
                }
                collect_last_use_var_names(body, last_uses, out);
            }
            _ => {}
        }
    }

    #[test]
    fn single_var_is_last_use() {
        assert_eq!(last_use_names("x"), vec!["x"]);
    }

    #[test]
    fn global_never_last_use() {
        assert!(last_use_names_with_globals("f", &["f"]).is_empty());
    }

    #[test]
    fn var_used_twice_only_second_is_last() {
        // (f x x) — first x is not last use, second x is
        let src = "(f x x)";
        let expr = parse_expr(src).unwrap();
        let globals: HashSet<String> = ["f"].iter().map(|s| s.to_string()).collect();
        let last_uses = compute_last_uses(&expr, &globals);

        // Find the two `x` Var spans
        if let Expr::Apply { args, .. } = &expr {
            assert!(!last_uses.contains(&args[0].span()), "first x should NOT be last use");
            assert!(last_uses.contains(&args[1].span()), "second x SHOULD be last use");
        }
    }

    #[test]
    fn let_binding_last_use_in_body() {
        // (let [x 1] x) — x in body is last use
        assert_eq!(last_use_names("(let [x 1] x)"), vec!["x"]);
    }

    #[test]
    fn let_var_used_in_binding_and_body() {
        // (let [y x] x) — both x refs; first is not last (x used in body), second is last
        let src = "(let [y x] x)";
        let expr = parse_expr(src).unwrap();
        let globals = HashSet::new();
        let last_uses = compute_last_uses(&expr, &globals);

        if let Expr::Let { bindings, body, .. } = &expr {
            assert!(!last_uses.contains(&bindings[0].1.span()), "x in binding should NOT be last use");
            assert!(last_uses.contains(&body.span()), "x in body SHOULD be last use");
        }
    }

    #[test]
    fn if_branches_conservative() {
        // (if c x x) — c is last-use, but both x refs are NOT last use
        // because branches are conservative (each branch assumes the other might run too)
        // Actually, for If: used_after for each branch is outer used_after (empty here)
        // So each x IS a last use within its branch
        let names = last_use_names_with_globals("(if c x x)", &[]);
        assert!(names.contains(&"c".to_string()));
        // Both branch x's should be last-use (independent branches, outer used_after is empty)
        assert_eq!(names.iter().filter(|n| *n == "x").count(), 2);
    }
}
