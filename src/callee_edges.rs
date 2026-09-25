//! The callee identities a binding records. Typecheck resolves each callable
//! reference once and stores its storage identity in the callable's `callees`;
//! redefinition blocking and the module cache's dependency edges both read that
//! fact here (`design/int/int.md` §7.6.1).

use cranelisp_types::{Binding, CodeStore, Decl, FQSymbol, Life};

/// Every callee recorded on `binding`'s callable, overload arms or macro
/// clauses, in either the template or the concrete life.
pub(crate) fn binding_callees<C: CodeStore>(
    binding: &Binding<C>,
) -> impl Iterator<Item = &FQSymbol> {
    let lives: Vec<&Life<C>> = match &binding.declaration {
        Decl::Callable(callable) => vec![&callable.arm.life],
        Decl::Overloaded(declaration) => declaration
            .arms
            .iter()
            .map(|arm| &arm.callable.life)
            .collect(),
        Decl::Macro(declaration) => declaration
            .clauses
            .iter()
            .map(|clause| &clause.callable.life)
            .collect(),
        _ => Vec::new(),
    };
    lives.into_iter().flat_map(life_callees)
}

fn life_callees<C: CodeStore>(life: &Life<C>) -> &[FQSymbol] {
    match life {
        Life::Template { callees, .. } | Life::Concrete { callees, .. } => callees,
        _ => &[],
    }
}
