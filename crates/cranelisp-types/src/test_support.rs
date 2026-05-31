//! Test-support symbol-table construction helpers (Tier 2).
//!
//! A **generic, content-agnostic** convenience for building a populated
//! [`SymbolTable<C, L>`](crate::SymbolTable) from declared entries, for use by
//! OTHER crates' tests — notably `cranelisp-typecheck`'s unit suite. It shares
//! only the Tier-1 [`ModuleEntry::def`](crate::ModuleEntry::def) constructor
//! with production code.
//!
//! # Delineation — feature-gated, NOT in the production baseline
//!
//! This module is compiled only under `#[cfg(any(test, feature =
//! "test-support"))]`. Pure `#[cfg(test)]` is crate-local and would not be
//! visible to a downstream crate's test build, so the `test-support` Cargo
//! feature is the visibility mechanism. The `public-api.txt` baseline is
//! generated WITHOUT `--features test-support`, so nothing here enters the
//! production contract. See `design/arch/bounded-contexts.md` §7.
//!
//! # Boundary — per-SymbolTable construction only
//!
//! [`SymbolTableBuilder`] builds **one** `SymbolTable`. It deliberately does
//! NOT orchestrate the multi-module `SymbolTables` DashMap, the session-level
//! `AtomicU32` next-type-id allocator, or any bootstrap ordering between
//! modules — that orchestration is typecheck's Tier-3 concern (per FIXME 0241
//! / 0239) because it is content- and bootstrap-aware (e.g. `macros/Sexp`
//! must resolve `primitives/Int` before the first `.cl` parses). Keeping this
//! tier to per-table construction is minimum mechanism (Principle 6): only the
//! genuinely generic, content-free piece lives here.
//!
//! # Content-agnostic
//!
//! There is no Option / IO / primitive scheme content here — those are
//! typecheck-owned (Tier 3). This builder takes whatever entries a test hands
//! it and assembles a table; it knows nothing about any specific module's
//! meaning.

use crate::{
    CodeStore, DefBuilder, DefKind, LinkerStore, ModuleEntry, ModuleFullPath, Scheme, Symbol,
    SymbolTable,
};

/// Generic, content-agnostic builder for a single
/// [`SymbolTable<C, L>`](crate::SymbolTable).
///
/// Start with [`SymbolTableBuilder::new(path)`](Self::new), add entries with
/// [`Self::entry`] (any [`ModuleEntry`]) or the [`Self::def`] convenience (a
/// thin wrapper over [`ModuleEntry::def`]), and finish with [`Self::build`].
///
/// Generic over `C: CodeStore` and `L: LinkerStore` so a test can build a
/// table at whichever instantiation it exercises (`<(), ()>` for typecheck's
/// usual case, `<Code, ()>` if a test drives an integration-flavoured table).
///
/// # Example
///
/// ```ignore
/// let table: SymbolTable = SymbolTableBuilder::new(ModuleFullPath::from("test"))
///     .def("id", scheme, DefKind::UserFn { constrained_fn: None })
///     .entry(Symbol::from("Some"), ModuleEntry::def(ctor_scheme, ctor_kind).build())
///     .build();
/// assert!(table.get("id").is_some());
/// ```
pub struct SymbolTableBuilder<C: CodeStore = (), L: LinkerStore = ()> {
    path: ModuleFullPath,
    entries: Vec<(Symbol, ModuleEntry<C>)>,
    _linker: std::marker::PhantomData<L>,
}

impl<C: CodeStore, L: LinkerStore> SymbolTableBuilder<C, L> {
    /// Begin building a table for module `path`.
    pub fn new(path: ModuleFullPath) -> Self {
        SymbolTableBuilder {
            path,
            entries: Vec::new(),
            _linker: std::marker::PhantomData,
        }
    }

    /// Add an arbitrary [`ModuleEntry`] under `name`.
    pub fn entry(mut self, name: impl Into<Symbol>, entry: ModuleEntry<C>) -> Self {
        self.entries.push((name.into(), entry));
        self
    }

    /// Convenience: add a [`ModuleEntry::Def`] under `name` with the Tier-1
    /// defaults (public visibility, no docstring/params/ast). For finer
    /// control over the Def fields, build the entry with
    /// [`ModuleEntry::def`] and pass it to [`Self::entry`].
    pub fn def(self, name: impl Into<Symbol>, scheme: Scheme, kind: DefKind) -> Self {
        let entry: ModuleEntry<C> = DefBuilder::new(scheme, kind).build();
        self.entry(name, entry)
    }

    /// Materialize the populated `SymbolTable<C, L>`.
    pub fn build(self) -> SymbolTable<C, L> {
        let mut table = SymbolTable::<C, L>::new_with_params(self.path);
        for (name, entry) in self.entries {
            table.insert(name, entry);
        }
        table
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Type;
    use std::collections::HashMap;

    fn mono_scheme(ty: Type) -> Scheme {
        Scheme { type_vars: vec![], constraints: HashMap::new(), ty }
    }

    // spec: design/arch/fixmes/0241 — Tier-2 SymbolTableBuilder round-trip
    #[test]
    fn builder_populates_and_round_trips() {
        let table: SymbolTable = SymbolTableBuilder::new(ModuleFullPath::from("test"))
            .def("id", mono_scheme(Type::Int), DefKind::UserFn { constrained_fn: None })
            .entry(
                Symbol::from("k"),
                ModuleEntry::def(mono_scheme(Type::Bool), DefKind::Primitive)
                    .docstring("constant")
                    .build(),
            )
            .build();

        assert_eq!(&*table.path, "test");
        assert!(table.get("id").is_some(), "def(...) entry must round-trip via lookup");
        match table.get("k") {
            Some(ModuleEntry::Def { docstring, .. }) => {
                assert_eq!(docstring.as_deref(), Some("constant"));
            }
            other => panic!("expected Def for 'k', got {:?}", other),
        }
        assert!(table.get("absent").is_none());
    }
}
