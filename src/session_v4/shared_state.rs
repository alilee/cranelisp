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
/// Recognizes through the same `recognize_macro_head` query as
/// `SymbolTableMacroResolver`, with no side effect: it loads no cached object.
/// A recognized macro whose clause is not in memory fails execution with
/// `MacroInvokeError::Aborted` (`design/int/int.md` §6.8).
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
        // `macro-availability-model.md` §5) — same path as the live
        // compile-time recognition; no second chain-walk copy.
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

// ---------------------------------------------------------------------------
// Recorded source states (design/int/repl-lifecycle.md §1.3.1, Unseen save)
// ---------------------------------------------------------------------------

impl super::SharedState {
    /// Record `state` as the state the session last loaded, reloaded or wrote
    /// for the source file at `path`.
    pub(crate) fn record_source(&self, path: &std::path::Path, state: crate::watch::FileState) {
        let key = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        self.recorded_sources.insert(key, state);
    }

    /// The state recorded for the source file at `path`, if any.
    pub(crate) fn recorded_source(
        &self,
        path: &std::path::Path,
    ) -> Option<crate::watch::FileState> {
        let key = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        self.recorded_sources.get(&key).map(|state| state.clone())
    }
}
