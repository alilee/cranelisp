//! CS-4 — the one-shot post-convergence site-fact annotation walk
//! (`design/typecheck/ownership-inference.md` §13.6(b), §2.3).
//!
//! Writes the converged escape / confined / provenance facts onto the stored
//! `codegen_view` body. Runs **once**, after both strata converge (never
//! mid-fixpoint — facts from a not-yet-converged environment could be stale).
//! `unique_static` is left `None` (increment-I pin, §10). `None` everywhere is
//! the conservative point — a backend ignoring any/all of these is correct.

use cranelisp_types::{MonoExpr, Span};

use super::transfer::SiteFacts;

/// Annotate `body` in place from `facts` (keyed by node span).
pub(crate) fn annotate(body: &mut MonoExpr, facts: &SiteFacts) {
    walk(body, facts);
}

fn set(span: Span, facts: &SiteFacts, escapes: &mut Option<bool>, confined: &mut Option<bool>) {
    if let Some(v) = facts.escapes.get(&span) {
        *escapes = Some(*v);
    }
    if let Some(v) = facts.confined.get(&span) {
        *confined = Some(*v);
    }
}

fn walk(expr: &mut MonoExpr, facts: &SiteFacts) {
    match expr {
        MonoExpr::IntLit { .. } | MonoExpr::FloatLit { .. } | MonoExpr::BoolLit { .. } => {}
        MonoExpr::Var { .. } => {}
        MonoExpr::StringLit { span, escapes, confined, .. } => {
            set(*span, facts, escapes, confined);
        }
        MonoExpr::Let { bindings, body, .. } => {
            for (_, rhs) in bindings {
                walk(rhs, facts);
            }
            walk(body, facts);
        }
        MonoExpr::If { cond, then_branch, else_branch, .. } => {
            walk(cond, facts);
            walk(then_branch, facts);
            walk(else_branch, facts);
        }
        MonoExpr::Lambda { body, span, escapes, confined, .. } => {
            set(*span, facts, escapes, confined);
            walk(body, facts);
        }
        MonoExpr::Apply { callee, args, span, escapes, confined, provenance, .. } => {
            set(*span, facts, escapes, confined);
            if let Some(root) = facts.provenance.get(span) {
                *provenance = Some(root.clone());
            }
            walk(callee, facts);
            for a in args {
                walk(a, facts);
            }
        }
        MonoExpr::Match { scrutinee, arms, .. } => {
            walk(scrutinee, facts);
            for arm in arms {
                if let Some(root) = facts.provenance.get(&arm.span) {
                    arm.provenance = Some(root.clone());
                }
                walk(&mut arm.body, facts);
            }
        }
        MonoExpr::VecLit { elements, span, escapes, confined, .. } => {
            set(*span, facts, escapes, confined);
            for e in elements {
                walk(e, facts);
            }
        }
        MonoExpr::Trace { body, .. } => walk(body, facts),
        MonoExpr::ParBind { bindings, body, .. } => {
            for (_, rhs) in bindings {
                walk(rhs, facts);
            }
            walk(body, facts);
        }
        MonoExpr::LaunchContinue { launched, continuation, .. } => {
            walk(launched, facts);
            walk(continuation, facts);
        }
        MonoExpr::ConstrADT { fields, span, escapes, confined, .. } => {
            set(*span, facts, escapes, confined);
            for f in fields {
                walk(f, facts);
            }
        }
    }
}
