//! `expand` — frontend's macro expansion entry point.
//!
//! Per `design/frontend/wave-3a-build-form.md` §5 and the facade
//! (`design/arch/facades/frontend.md` §"Free functions" — `expand`):
//!
//! ```ignore
//! pub fn expand<C, L>(sexp: Sexp, symbol_tables: &SymbolTables<C, L>)
//!     -> Result<Sexp, ExpansionError>
//! where C: CodeStore, L: LinkerStore;
//! ```
//!
//! ## Wave 3a-β scope (deferred invocation; FIXME 0175)
//!
//! Per facade contract, `expand` should invoke registered macros via JIT'd
//! code addresses found through `symbol_tables`. **Invocation requires
//! `cranelisp-runtime` access (marshal + signal handling), which the
//! frontend's allowed-deps statement forbids.** The full invocation path
//! is therefore deferred to `/arch`'s resolution of FIXME 0175.
//!
//! This Wave 3a-β delivery is the structural skeleton:
//!   - Quasiquote desugaring (`expand_quasiquotes`) runs unconditionally
//!     once at the top of expansion.
//!   - Tree traversal recognises macro-head positions — bare-symbol macros
//!     and `(macro-name args…)` forms — by looking up
//!     `ModuleEntry::Def { kind: DefKind::Macro { clauses_meta }, .. }`
//!     in `symbol_tables` (post-S69 Submission 22: the sibling
//!     `ModuleEntry::Macro` variant is retired; per S69 Submission 13 macro
//!     storage is unified under the `Def` shape).
//!   - **Every recognised macro head returns
//!     `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))`** —
//!     uniform Gap per facade §"expand". Per the orchestrator-side retry
//!     protocol (facades/int.md §"process_form"), the orchestrator
//!     handles the wait and re-dispatches; in Wave 3a-β, the orchestrator
//!     keeps calling `src/expander.rs::expand_sexp_recursive` for the
//!     actual invocation while this skeleton stays inert in the gap
//!     return path.
//!   - The depth limit (`EXPANSION_DEPTH_LIMIT = 100`) is preserved and
//!     surfaces as `Malformed { message, span }` rather than silent
//!     truncation, per master design §5.2.
//!   - The function is generic over `<C: CodeStore, L: LinkerStore>` so
//!     it remains C/L-blind; consumers can pass `SymbolTables<(), ()>`
//!     in tests and `SymbolTables<Code, ()>` in the integration layer.
//!
//! ## Module FQ resolution
//!
//! Bare and FQ macro-head symbols are resolved through `symbol_tables`:
//! - `"name"` looks up `ModuleEntry::Def { kind: DefKind::Macro, .. }` in
//!   each module's table; an `Import` entry (post-S69 Submission 22, the
//!   former `Reexport` variant collapsed into `Import { visibility: Public }`)
//!   triggers a single chain follow to find the home module per Principle 17.
//! - `"module.path/name"` (or `"module/name"`) parses out the FQ shape
//!   and resolves directly.
//!
//! If a name resolves to neither a macro nor a `Var` (no symbol-table
//! entry at all), it is left in place as a possible function call —
//! `build_form`/`build_expr` will fail downstream with a clearer error.

use cranelisp_types::{
    CodeStore, DefKind, FQSymbol, LinkerStore, ModuleAliases, ModuleEntry, ModuleFullPath,
    ResolutionGap, Sexp, Span, Symbol, SymbolTable, SymbolTables,
};

use crate::quasiquote::expand_quasiquotes;

/// Maximum nesting depth for macro expansion.
///
/// A defensive guard against infinite-recursive macro definitions. On
/// reaching the limit, `expand` returns `Malformed` with a diagnostic
/// message rather than silently truncating.
pub const EXPANSION_DEPTH_LIMIT: usize = 100;

/// Typed error returned by macro expansion.
///
/// `Gap(ResolutionGap)` is the dominant variant during Wave 3a's
/// gap-orchestration loop: when expansion needs an in-mem macro that
/// has not yet been JIT'd, it returns `Gap(ResolutionGap::MacroInMem)`
/// and `int::process_form` priority-boosts that fq + waits.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum ExpansionError {
    /// Cross-cutting "this dependency isn't ready yet" — typically
    /// `ResolutionGap::MacroInMem(fq)` from frontend's expand path.
    Gap(ResolutionGap),
    /// Macro syntax malformed (bad params, malformed body, depth-limit
    /// exceeded, etc.).
    Malformed { message: String, span: Span },
    /// Macro body raised an error during expansion (panic in clause body,
    /// type-failed clause). Reserved for the future-state invocation
    /// path; not produced by the Wave 3a-β skeleton.
    MacroAborted {
        fq: FQSymbol,
        message: String,
        span: Span,
    },
}

impl std::fmt::Display for ExpansionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpansionError::Gap(g) => write!(f, "expansion gap: {g:?}"),
            ExpansionError::Malformed { message, span } => {
                write!(f, "malformed macro at {span}: {message}")
            }
            ExpansionError::MacroAborted { fq, message, span } => {
                write!(f, "macro `{fq:?}` aborted at {span}: {message}")
            }
        }
    }
}

impl std::error::Error for ExpansionError {}

// ---------------------------------------------------------------------------
// `expand` — public entry
// ---------------------------------------------------------------------------

/// Recursively expand macro calls in a Sexp tree.
///
/// Quasiquote desugaring runs unconditionally before macro dispatch.
///
/// Per facade contract:
/// - Returns `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` on
///   any recognised macro head — uniform Gap.
/// - Returns `Err(ExpansionError::Malformed { … })` on depth-limit
///   exceeded or other shape failures surfaced during traversal.
/// - Otherwise returns the (quasiquote-desugared) sexp unchanged.
///
/// Side-effect-free for dependency resolution: never blocks, never calls
/// the scheduler, never mutates `symbol_tables`.
///
/// The `module_aliases` parameter carries the session-level alias table
/// per BC §7 ("Module aliases live at session level") + spec §8.6.6.
/// Once FIXME 0175 resolves and the live invocation path migrates into
/// `cranelisp-frontend`, alias resolution at the macro-head lookup
/// becomes load-bearing. For now the parameter is wiring for later.
// FIXME 0175 — alias traversal lives in src/expander.rs until marshal-deps resolve
pub fn expand<C, L>(
    sexp: Sexp,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
) -> Result<Sexp, ExpansionError>
where
    C: CodeStore,
    L: LinkerStore,
{
    let desugared = expand_quasiquotes(&sexp).map_err(|err| ExpansionError::Malformed {
        message: format!("quasiquote desugaring failed: {err}"),
        span: sexp.span(),
    })?;
    expand_recursive(desugared, symbol_tables, module_aliases, 0)
}

// `module_aliases` is threaded through recursion but not yet consulted at
// the lookup — FIXME 0175 (alias traversal lives in src/expander.rs until
// marshal-deps resolve). The parameter is structural wiring for later.
#[allow(clippy::only_used_in_recursion)]
fn expand_recursive<C, L>(
    sexp: Sexp,
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    depth: usize,
) -> Result<Sexp, ExpansionError>
where
    C: CodeStore,
    L: LinkerStore,
{
    if depth > EXPANSION_DEPTH_LIMIT {
        return Err(ExpansionError::Malformed {
            message: format!(
                "macro expansion depth limit ({EXPANSION_DEPTH_LIMIT}) exceeded"
            ),
            span: sexp.span(),
        });
    }

    match sexp {
        Sexp::List(children, span) if !children.is_empty() => {
            // Macro call: head is a bare symbol that resolves to a
            // `ModuleEntry::Def { kind: DefKind::Macro { .. }, .. }` (post-S69
            // Submission 22 — the sibling `ModuleEntry::Macro` variant is
            // retired; per Submission 13 macros share the unified Def shape).
            if let Sexp::Symbol(ref name, sym_span) = children[0]
                && let Some(fq) = lookup_macro_fq(name, sym_span, symbol_tables)
            {
                return Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)));
            }
            // Otherwise recurse into children. `depth + 1` per child descent —
            // bounds defensive against pathologically deep source structures
            // (per master design §5.2 the limit is a defensive guard, not a
            // contract guarantee).
            let expanded: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_recursive(c, symbol_tables, module_aliases, depth + 1))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::List(expanded, span))
        }
        Sexp::Symbol(ref name, span) => {
            // Bare-symbol zero-arg macro.
            if let Some(fq) = lookup_macro_fq(name, span, symbol_tables) {
                return Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)));
            }
            Ok(sexp)
        }
        Sexp::Bracket(children, span) => {
            let expanded: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_recursive(c, symbol_tables, module_aliases, depth + 1))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::Bracket(expanded, span))
        }
        _ => Ok(sexp),
    }
}

/// Resolve a symbol name to a fully-qualified macro reference if any.
///
/// Recognises two shapes:
/// 1. **FQ**: `"module.path/name"` parses out the module + name and probes
///    `symbol_tables[module]` for a
///    `ModuleEntry::Def { kind: DefKind::Macro { .. }, .. }` (chasing one
///    `Import` hop if encountered, per Principle 17 — the prior `Reexport`
///    variant collapsed into `Import { visibility: Public }` at S69
///    Submission 22).
/// 2. **Bare**: `"name"` probes every module in `symbol_tables` for a
///    matching `Def`-shape macro entry. The first match wins.
///
/// Returns `None` if no module contains a `Def`-shape macro entry with this
/// name — bare function/variable references fall through to the caller.
/// Post-S69 Submission 13 (macro-unification), macro storage is uniformly
/// `Def { kind: DefKind::Macro { clauses_meta }, .. }`; the retired sibling
/// `ModuleEntry::Macro` variant is no longer probed.
///
/// Per facade §59 + BC §7 §"Module aliases live at session level" +
/// spec §8.6.6 the FQ shape may need to traverse a `ModuleAliasEntry`
/// (longest-prefix-match against the queried `module_path`) before
/// probing `symbol_tables`. That step is structurally pending — the
/// `module_aliases` parameter is now wired into `expand` but not yet
/// consulted at this lookup. FIXME 0175 tracks the marshal-deps gap
/// that keeps the live invocation path in `src/expander.rs`; alias
/// traversal lands in this helper once the invocation path migrates.
fn lookup_macro_fq<C, L>(
    name: &str,
    _span: Span,
    symbol_tables: &SymbolTables<C, L>,
) -> Option<FQSymbol>
where
    C: CodeStore,
    L: LinkerStore,
{
    // FQ shape: "module.path/name".
    if let Some((mod_part, name_part)) = name.rsplit_once('/')
        && !name_part.contains('/')
    {
        let module_path = ModuleFullPath::from(mod_part);
        if let Some(entry) = symbol_tables.get(&module_path)
            && macro_entry_present(&entry, name_part, symbol_tables)
        {
            return Some(FQSymbol {
                module: module_path,
                symbol: Symbol::from(name_part),
            });
        }
        return None;
    }

    // Bare shape: probe every module's table.
    for entry in symbol_tables.iter() {
        let module_path = entry.key().clone();
        if macro_entry_present(entry.value(), name, symbol_tables) {
            return Some(FQSymbol {
                module: module_path,
                symbol: Symbol::from(name),
            });
        }
    }
    None
}

/// Returns true if the table contains a
/// `ModuleEntry::Def { kind: DefKind::Macro { .. }, .. }` for `name`
/// — directly, or by chasing a single `Import` hop (the prior `Reexport`
/// variant collapsed into `Import { visibility: Public }` at S69
/// Submission 22; macro storage unified into the `Def` shape at S69
/// Submission 13).
fn macro_entry_present<C, L>(
    table: &SymbolTable<C, L>,
    name: &str,
    symbol_tables: &SymbolTables<C, L>,
) -> bool
where
    C: CodeStore,
    L: LinkerStore,
{
    match table.get(name) {
        Some(ModuleEntry::Def { kind, .. }) if matches!(**kind, DefKind::Macro { .. }) => true,
        Some(ModuleEntry::Import { source, .. }) => {
            // One-hop chain follow per Principle 17 + Decision 45. Walks
            // `Import` edges regardless of visibility — the prior
            // `ModuleEntry::Reexport` variant collapsed into
            // `Import { visibility: Public }`. Avoids infinite loops by NOT
            // recursing further: an Import-of-an-Import is treated as a
            // non-macro for resolution purposes (the typecheck-side expects
            // a single hop to a real entry).
            //
            // Per S69 Submission 13 (macro-unification), macro storage rotated
            // from the retired `ModuleEntry::Macro` variant into
            // `ModuleEntry::Def { kind: DefKind::Macro { clauses_meta }, .. }`
            // (per-clause bodies live as separate `Def`s under mangled
            // `{macro}$clause-{N}` names). This row is the lookup-shape
            // rotation only — invocation-vs-Gap policy remains FIXME 0175.
            if let Some(home) = symbol_tables.get(&source.module) {
                matches!(
                    home.get(source.symbol.as_ref()),
                    Some(ModuleEntry::Def { kind, .. }) if matches!(**kind, DefKind::Macro { .. })
                )
            } else {
                false
            }
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{
        MacroClauseInfo, ModuleFullPath, Scheme, Span, Symbol, Type, TypeName, Visibility,
    };
    use dashmap::DashMap;
    use std::collections::HashMap;
    use std::sync::Arc;

    /// Build a tiny `SymbolTable<(), ()>` carrying a single macro entry
    /// (post-S69 Submission 13: `ModuleEntry::Def { kind: DefKind::Macro }`).
    fn module_with_macro(path: &str, macro_name: &str) -> (ModuleFullPath, SymbolTable<(), ()>) {
        let module_path = ModuleFullPath::from(path);
        let mut symbols: HashMap<Symbol, ModuleEntry<()>> = HashMap::new();
        symbols.insert(
            Symbol::from(macro_name),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Int,
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::Macro {
                    clauses_meta: vec![MacroClauseInfo {
                        params: vec![],
                        rest_param: None,
                    }],
                }),
                callees: vec![],
                got_slot: None,
                trait_origin: None,
                seq: 0,
                ast: None,
                code: None,
            },
        );
        let table = SymbolTable {
            path: module_path.clone(),
            symbols,
            next_got_slot: 0,
            next_seq: 0,
            got: Arc::new(cranelisp_types::GotTable::new()),
            imports: vec![],
            exports: vec![],
            platforms: vec![],
            submodules: vec![],
            linker: None,
            schema_version: 0,
        };
        (module_path, table)
    }

    /// Build a `SymbolTables<(), ()>` carrying one module + one macro.
    fn tables_with_macro(module_path: &str, macro_name: &str) -> SymbolTables<(), ()> {
        let tables: SymbolTables<(), ()> = DashMap::new();
        let (path, table) = module_with_macro(module_path, macro_name);
        tables.insert(path, table);
        tables
    }

    /// Empty tables.
    fn empty_tables() -> SymbolTables<(), ()> {
        DashMap::new()
    }

    /// Empty module aliases — FIXME 0175 keeps alias traversal in
    /// src/expander.rs; the parameter is wiring for later.
    fn empty_aliases() -> ModuleAliases {
        DashMap::new()
    }

    // spec: 09-macros.md §9 — `expand` is side-effect free + returns owned sexp.
    #[test]
    fn no_macros_passthrough() {
        let tables = empty_tables();
        let sexp = Sexp::Int(42, Span::SYNTHETIC);
        let out = expand(sexp.clone(), &tables, &empty_aliases()).unwrap();
        match (sexp, out) {
            (Sexp::Int(a, _), Sexp::Int(b, _)) => assert_eq!(a, b),
            other => panic!("expected Int passthrough, got {other:?}"),
        }
    }

    // spec: 09-macros.md §9 — list with no macro head recurses + returns.
    #[test]
    fn list_no_macro_head_returns_list() {
        let tables = empty_tables();
        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("non-macro-fn".to_string(), Span::SYNTHETIC),
                Sexp::Int(1, Span::SYNTHETIC),
                Sexp::Int(2, Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let out = expand(sexp, &tables, &empty_aliases()).unwrap();
        match out {
            Sexp::List(children, _) => assert_eq!(children.len(), 3),
            other => panic!("expected List, got {other:?}"),
        }
    }

    // facade frontend.md §"expand" — bare macro head returns Gap(MacroInMem).
    #[test]
    fn list_with_macro_head_returns_gap() {
        let tables = tables_with_macro("user", "my-macro");
        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("my-macro".to_string(), Span::SYNTHETIC),
                Sexp::Int(1, Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let err = expand(sexp, &tables, &empty_aliases()).unwrap_err();
        match err {
            ExpansionError::Gap(ResolutionGap::MacroInMem(fq)) => {
                assert_eq!(fq.module.as_ref(), "user");
                assert_eq!(fq.symbol.as_ref(), "my-macro");
            }
            other => panic!("expected Gap(MacroInMem), got {other:?}"),
        }
    }

    // facade frontend.md §"expand" — bare symbol zero-arg macro returns Gap.
    #[test]
    fn bare_symbol_zero_arg_macro_returns_gap() {
        let tables = tables_with_macro("user", "current-line");
        let sexp = Sexp::Symbol("current-line".to_string(), Span::SYNTHETIC);
        let err = expand(sexp, &tables, &empty_aliases()).unwrap_err();
        match err {
            ExpansionError::Gap(ResolutionGap::MacroInMem(fq)) => {
                assert_eq!(fq.symbol.as_ref(), "current-line");
            }
            other => panic!("expected Gap(MacroInMem), got {other:?}"),
        }
    }

    // facade frontend.md §"expand" — FQ macro reference returns Gap with
    // module taken from the FQ path, not from bare-name probing.
    #[test]
    fn fq_macro_head_returns_gap() {
        let tables = tables_with_macro("macros", "when");
        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("macros/when".to_string(), Span::SYNTHETIC),
                Sexp::Symbol("true".to_string(), Span::SYNTHETIC),
                Sexp::Int(1, Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let err = expand(sexp, &tables, &empty_aliases()).unwrap_err();
        match err {
            ExpansionError::Gap(ResolutionGap::MacroInMem(fq)) => {
                assert_eq!(fq.module.as_ref(), "macros");
                assert_eq!(fq.symbol.as_ref(), "when");
            }
            other => panic!("expected Gap(MacroInMem), got {other:?}"),
        }
    }

    // facade frontend.md §"expand" — Import-chain hop resolves through to
    // the home module's macro entry (Principle 17 single-hop probe).
    #[test]
    fn import_hop_resolves_to_home_macro() {
        let home = ModuleFullPath::from("macros");
        let user = ModuleFullPath::from("user");
        let (_, home_table) = module_with_macro("macros", "when");

        // user's table contains an Import { source: macros/when } entry.
        let mut user_symbols: HashMap<Symbol, ModuleEntry<()>> = HashMap::new();
        user_symbols.insert(
            Symbol::from("when"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: home.clone(),
                    symbol: Symbol::from("when"),
                },
                visibility: Visibility::Public,
            },
        );
        let user_table = SymbolTable {
            path: user.clone(),
            symbols: user_symbols,
            next_got_slot: 0,
            next_seq: 0,
            got: Arc::new(cranelisp_types::GotTable::new()),
            imports: vec![],
            exports: vec![],
            platforms: vec![],
            submodules: vec![],
            linker: None,
            schema_version: 0,
        };
        let tables: SymbolTables<(), ()> = DashMap::new();
        tables.insert(home, home_table);
        tables.insert(user, user_table);

        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("when".to_string(), Span::SYNTHETIC),
                Sexp::Symbol("true".to_string(), Span::SYNTHETIC),
                Sexp::Int(1, Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let err = expand(sexp, &tables, &empty_aliases()).unwrap_err();
        match err {
            ExpansionError::Gap(ResolutionGap::MacroInMem(fq)) => {
                // The FQ returned should be from whatever module the
                // probe found first — either the user table (via Import)
                // or the macros table (direct). Both are valid; assert
                // the symbol is correct.
                assert_eq!(fq.symbol.as_ref(), "when");
            }
            other => panic!("expected Gap(MacroInMem), got {other:?}"),
        }
    }

    // facade frontend.md §"expand" — bracketed sexp with macro head returns
    // Gap from nested expansion.
    #[test]
    fn bracket_recursion_yields_gap_on_nested_macro() {
        let tables = tables_with_macro("user", "inner-macro");
        let sexp = Sexp::Bracket(
            vec![Sexp::List(
                vec![
                    Sexp::Symbol("inner-macro".to_string(), Span::SYNTHETIC),
                    Sexp::Int(7, Span::SYNTHETIC),
                ],
                Span::SYNTHETIC,
            )],
            Span::SYNTHETIC,
        );
        let err = expand(sexp, &tables, &empty_aliases()).unwrap_err();
        assert!(matches!(err, ExpansionError::Gap(_)));
    }

    // facade frontend.md §"expand" — non-Macro entries (e.g. Def) do NOT
    // produce a Gap; the form passes through as a function call.
    #[test]
    fn non_macro_entry_passes_through() {
        let path = ModuleFullPath::from("user");
        let mut symbols: HashMap<Symbol, ModuleEntry<()>> = HashMap::new();
        // A Def entry for "f" — function, not macro. Must not produce Gap.
        symbols.insert(
            Symbol::from("f"),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Int,
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn {
                    constrained_fn: None,
                }),
                callees: vec![],
                got_slot: None,
                trait_origin: None,
                seq: 0,
                ast: None,
                code: None,
            },
        );
        let table = SymbolTable {
            path: path.clone(),
            symbols,
            next_got_slot: 0,
            next_seq: 0,
            got: Arc::new(cranelisp_types::GotTable::new()),
            imports: vec![],
            exports: vec![],
            platforms: vec![],
            submodules: vec![],
            linker: None,
            schema_version: 0,
        };
        let tables: SymbolTables<(), ()> = DashMap::new();
        tables.insert(path, table);

        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("f".to_string(), Span::SYNTHETIC),
                Sexp::Int(1, Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let out = expand(sexp, &tables, &empty_aliases()).expect("function call must not produce Gap");
        // Returned shape: the same List wrapping a Var head + Int.
        match out {
            Sexp::List(children, _) => assert_eq!(children.len(), 2),
            other => panic!("expected List, got {other:?}"),
        }
    }

    // facade frontend.md §"expand" — depth limit yields Malformed, not
    // silent truncation. (Tested by recursing into a deeply-nested
    // synthetic List; no macros required because the depth check fires
    // on recursion descent.)
    //
    // NB: the depth check fires before list recursion descends — we
    // construct a structure deep enough to trigger.
    #[test]
    fn depth_limit_yields_malformed() {
        let tables = empty_tables();
        // Build a list nested EXPANSION_DEPTH_LIMIT + 5 deep.
        let mut inner = Sexp::Int(1, Span::SYNTHETIC);
        for _ in 0..(EXPANSION_DEPTH_LIMIT + 5) {
            inner = Sexp::List(vec![inner], Span::SYNTHETIC);
        }
        let err = expand(inner, &tables, &empty_aliases()).unwrap_err();
        match err {
            ExpansionError::Malformed { message, .. } => {
                assert!(
                    message.contains("depth limit"),
                    "expected depth-limit message, got: {message}"
                );
            }
            other => panic!("expected Malformed, got {other:?}"),
        }
    }

    // facade frontend.md §"expand" — `Send + Sync` (free function takes
    // `&SymbolTables`; multiple workers may call concurrently per Decision 38).
    #[test]
    fn expand_is_send_sync() {
        fn assert_send_sync<F: Send + Sync>(_: F) {}
        // Take a function pointer of the right shape and assert its
        // marker traits; this catches Send/Sync regressions at compile time.
        let f: fn(Sexp, &SymbolTables<(), ()>, &ModuleAliases) -> Result<Sexp, ExpansionError> =
            expand::<(), ()>;
        assert_send_sync(f);
    }

    // facade frontend.md §"Types originated here" — `SymbolTables<C, L>`
    // is the alias frontend exposes; works for `<(), ()>` (typecheck and
    // tests) without naming Code/Linker.
    #[test]
    fn symbol_tables_alias_works_with_unit_params() {
        let _tables: SymbolTables<(), ()> = DashMap::new();
    }

    // spec: 09-macros.md — `expand_quasiquotes` runs before macro dispatch,
    // so a quasiquote'd form that contains no macros is returned with the
    // quasiquote desugared.
    #[test]
    fn quasiquotes_desugared_before_macro_dispatch() {
        let tables = empty_tables();
        // Build `(quasiquote 42)` — expand should desugar this through
        // expand_quasiquotes and return the resulting Sexp without
        // producing a Gap.
        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("quasiquote".to_string(), Span::SYNTHETIC),
                Sexp::Int(42, Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        // We don't assert the exact desugared shape — just that expand
        // succeeds. The shape contract belongs to `expand_quasiquotes`,
        // which is tested separately in `quasiquote.rs`.
        let _ = expand(sexp, &tables, &empty_aliases()).expect("quasiquote desugaring should succeed");
        let _ = TypeName::from("Unused"); // touch import to keep the use list tidy
    }
}
