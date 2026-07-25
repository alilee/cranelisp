// session_v4::shared_state — `SharedState`-adjacent behavior (S87 §2.1).
//
// `ReadOnlyMacroResolver` (the `/expand` read-only recognizer) is the one piece
// of `SharedState`-adjacent behavior that is NOT a `CompilerSession` method and
// NOT a DTO — it borrows the shared maps directly. The `SharedState` struct
// definition itself stays in the parent (§2.0 — single definition site for the
// sibling `impl CompilerSession` blocks). Moved verbatim from `session_v4.rs`
// (S87 §2.1).

use cranelisp_types::{CranelispError, FQSymbol, ModuleFullPath, Span};

use crate::code::SessionSymbolTable;

// ---------------------------------------------------------------------------
// ReadOnlyMacroResolver — for /expand slash command
// ---------------------------------------------------------------------------

/// Read-only macro resolver for the /expand slash command.
///
/// Same lookup logic as `SymbolTableMacroResolver` (follows Import/Reexport
/// chains) but never triggers compilation. If a macro's clauses are not
/// compiled, returns `Ok(None)` (silently skipped).
pub(crate) struct ReadOnlyMacroResolver<'a> {
    pub(crate) symbol_tables: &'a dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    pub(crate) module_aliases: &'a cranelisp_types::ModuleAliases,
    /// Per-module prelude-fallback bits — so `/expand` recognizes a
    /// prelude-provided macro from a user module via the implicit outer scope
    /// (S78 §2; public-only per I-1), matching the live compile-time path.
    pub(crate) prelude_fallback: &'a cranelisp_typecheck::PreludeFallback,
    pub(crate) current_module: ModuleFullPath,
}

impl crate::expander::MacroResolver for ReadOnlyMacroResolver<'_> {
    fn symbol_tables(&self) -> &dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
        self.symbol_tables
    }

    fn recognize(&mut self, name: &str, span: Span) -> Result<Option<FQSymbol>, CranelispError> {
        // RECOGNITION via the LOCKED types primitive (committed `View`,
        // `macro-availability-model.md` §0.7) — same path as the live
        // compile-time recognition; no second chain-walk copy. Read-only:
        // no on-demand compilation. If the macro's clauses are not already in
        // memory, the executor (`JitMacroExpander::invoke`) surfaces a clear
        // `Aborted` — `/expand` is only meaningful after the macro is defined
        // and compiled, which the REPL flow guarantees for a prior input.
        crate::expander::recognize_macro_head(
            self.symbol_tables,
            self.module_aliases,
            self.prelude_fallback,
            &self.current_module,
            name,
            span,
        )
    }
}
