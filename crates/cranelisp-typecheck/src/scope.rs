//! Scope stack for lexical scoping.
//!
//! Uses push/pop instead of env.clone() (addresses audit MED-4).
//! Lookup walks frames top-to-bottom so inner scopes shadow outer.

use std::collections::{HashMap, HashSet};

use cranelisp_types::{Scheme, Span, Symbol, TypeId, free_vars};

/// A stack of lexical scope frames. Each frame maps names to type schemes.
/// Lookup walks from the top (innermost) to bottom (outermost).
///
/// **Binder-identity provenance (S114 carrier flip, `VarRef::Local`).** A
/// parallel `frame_spans` records the span of the **binding form** that
/// introduced each frame (the `let`/`fn`/`defn`/match-arm node — every binder
/// in one frame shares that form's span, the honest grain since per-binder
/// spans do not exist on the AST for params; `design/arch/typed-resolution-carrier.md`
/// §2(a)). `binding_form_span(name)` reads it so `record_reference_target` can
/// stamp `VarRef::Local { binder, binding_span }` for a local reference. The
/// base (module) frame carries [`Span::SYNTHETIC`] — it never sources a
/// `VarRef::Local` (module-level defs resolve via the table → `Global`).
#[derive(Debug, Clone)]
pub struct ScopeStack {
    frames: Vec<HashMap<Symbol, Scheme>>,
    /// Parallel to `frames`: the binding-form span each frame was pushed with.
    frame_spans: Vec<Span>,
}

impl ScopeStack {
    /// Create a new scope stack with one empty frame (the module-level scope).
    pub fn new() -> Self {
        ScopeStack {
            frames: vec![HashMap::new()],
            frame_spans: vec![Span::SYNTHETIC],
        }
    }

    /// Push a new empty scope frame introduced by the binding form at
    /// `binding_span` (the `let`/`fn`/`defn`/match-arm node). Every binder bound
    /// into this frame shares that span as its `VarRef::Local` binding-form
    /// provenance.
    pub fn push_scope(&mut self, binding_span: Span) {
        self.frames.push(HashMap::new());
        self.frame_spans.push(binding_span);
    }

    /// Pop the topmost scope frame.
    /// Panics if trying to pop the base frame (logic error).
    pub fn pop_scope(&mut self) {
        debug_assert!(
            self.frames.len() > 1,
            "invariant: cannot pop the base scope frame"
        );
        self.frames.pop();
        self.frame_spans.pop();
    }

    /// The binding-FORM span of the frame in which `name` first resolves
    /// (innermost-first), for `VarRef::Local { binding_span }`. `None` if `name`
    /// is unbound in any frame. Reuses [`Self::lookup_frame`]'s index so the
    /// span read agrees with the scheme lookup.
    pub fn binding_form_span(&self, name: &str) -> Option<Span> {
        self.lookup_frame(name).map(|idx| self.frame_spans[idx])
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

    /// The frame INDEX (0 = base) at which `name` first resolves, searching
    /// innermost-first. `None` if `name` is unbound. Used by the self-recursion
    /// carrier carve-out to tell the enclosing defn's own recursion binding
    /// (installed in `check_defn_body`'s frame) apart from a same-named nested
    /// `let`/`fn` binding that resolves in a DEEPER frame (FIXME 0619 item 2).
    pub fn lookup_frame(&self, name: &str) -> Option<usize> {
        self.frames
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, frame)| frame.contains_key(name).then_some(i))
    }

    /// Index of the current (topmost) frame. Captured by `check_defn_body` to
    /// mark the frame that holds the enclosing defn's recursion binding.
    pub fn top_frame_index(&self) -> usize {
        self.frames.len() - 1
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
