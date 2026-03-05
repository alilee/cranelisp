//! Scope stack for lexical scoping.
//!
//! Uses push/pop instead of env.clone() (addresses audit MED-4).
//! Lookup walks frames top-to-bottom so inner scopes shadow outer.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{Scheme, Symbol, TypeId, free_vars};

/// A stack of lexical scope frames. Each frame maps names to type schemes.
/// Lookup walks from the top (innermost) to bottom (outermost).
#[derive(Debug, Clone)]
pub struct ScopeStack {
    frames: Vec<HashMap<Symbol, Scheme>>,
}

impl ScopeStack {
    /// Create a new scope stack with one empty frame (the module-level scope).
    pub fn new() -> Self {
        ScopeStack {
            frames: vec![HashMap::new()],
        }
    }

    /// Push a new empty scope frame.
    pub fn push_scope(&mut self) {
        self.frames.push(HashMap::new());
    }

    /// Pop the topmost scope frame.
    /// Panics if trying to pop the base frame (logic error).
    pub fn pop_scope(&mut self) {
        debug_assert!(
            self.frames.len() > 1,
            "invariant: cannot pop the base scope frame"
        );
        self.frames.pop();
    }

    /// Bind a name in the current (topmost) scope frame.
    pub fn bind(&mut self, name: Symbol, scheme: Scheme) {
        if let Some(top) = self.frames.last_mut() {
            top.insert(name, scheme);
        }
    }

    /// Look up a name, searching from innermost to outermost scope.
    pub fn lookup(&self, name: &str) -> Option<&Scheme> {
        for frame in self.frames.iter().rev() {
            if let Some(scheme) = frame.get(name) {
                return Some(scheme);
            }
        }
        None
    }

    /// Collect all free type variables across all scope frames.
    /// Used by `generalize` to determine which variables are "free in the environment".
    pub fn free_vars_in_env(&self) -> HashSet<TypeId> {
        let mut result = HashSet::new();
        for frame in &self.frames {
            for scheme in frame.values() {
                // Free vars in a scheme are those in the type but NOT quantified
                let ty_fv = free_vars(&scheme.ty);
                let quantified: HashSet<TypeId> = scheme.vars.iter().copied().collect();
                for v in ty_fv {
                    if !quantified.contains(&v) {
                        result.insert(v);
                    }
                }
            }
        }
        result
    }

    /// Return the number of frames (for snapshot/restore).
    #[allow(dead_code)]
    pub fn depth(&self) -> usize {
        self.frames.len()
    }

    /// Number of entries in the base (module-level) frame.
    #[allow(dead_code)]
    pub fn base_frame_len(&self) -> usize {
        self.frames.first().map_or(0, |f| f.len())
    }
}

impl Default for ScopeStack {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Type;

    fn mono(ty: Type) -> Scheme {
        Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty,
        }
    }

    #[test]
    fn test_basic_lookup() {
        let mut stack = ScopeStack::new();
        stack.bind(Symbol::from("x"), mono(Type::Int));
        assert_eq!(stack.lookup("x").unwrap().ty, Type::Int);
    }

    #[test]
    fn test_shadowing() {
        let mut stack = ScopeStack::new();
        stack.bind(Symbol::from("x"), mono(Type::Int));
        stack.push_scope();
        stack.bind(Symbol::from("x"), mono(Type::Bool));
        assert_eq!(stack.lookup("x").unwrap().ty, Type::Bool);
        stack.pop_scope();
        assert_eq!(stack.lookup("x").unwrap().ty, Type::Int);
    }

    #[test]
    fn test_lookup_outer_scope() {
        let mut stack = ScopeStack::new();
        stack.bind(Symbol::from("x"), mono(Type::Int));
        stack.push_scope();
        stack.bind(Symbol::from("y"), mono(Type::Bool));
        // Can still see x from outer scope
        assert_eq!(stack.lookup("x").unwrap().ty, Type::Int);
        assert_eq!(stack.lookup("y").unwrap().ty, Type::Bool);
        stack.pop_scope();
        assert!(stack.lookup("y").is_none());
    }

    #[test]
    fn test_lookup_not_found() {
        let stack = ScopeStack::new();
        assert!(stack.lookup("x").is_none());
    }

    #[test]
    fn test_free_vars_in_env() {
        let mut stack = ScopeStack::new();
        // x : t0  (monomorphic -- t0 is free in env)
        stack.bind(Symbol::from("x"), mono(Type::Var(0)));
        let fv = stack.free_vars_in_env();
        assert!(fv.contains(&0));

        // y : forall [t1]. t1 -> t1  (t1 is quantified, not free)
        stack.bind(
            Symbol::from("y"),
            Scheme {
                vars: vec![1],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![Type::Var(1)], Box::new(Type::Var(1))),
            },
        );
        let fv = stack.free_vars_in_env();
        assert!(fv.contains(&0));
        assert!(!fv.contains(&1));
    }

    #[test]
    fn test_push_pop_depth() {
        let mut stack = ScopeStack::new();
        assert_eq!(stack.depth(), 1);
        stack.push_scope();
        assert_eq!(stack.depth(), 2);
        stack.push_scope();
        assert_eq!(stack.depth(), 3);
        stack.pop_scope();
        assert_eq!(stack.depth(), 2);
        stack.pop_scope();
        assert_eq!(stack.depth(), 1);
    }
}
