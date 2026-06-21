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
                let quantified: HashSet<TypeId> = scheme.type_vars.iter().copied().collect();
                for v in ty_fv {
                    if !quantified.contains(&v) {
                        result.insert(v);
                    }
                }
            }
        }
        result
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
mod tests;
