// Slash command handlers for the REPL.
//
// Each handler implements one of the /help, /sig, /doc, /type, /info, /list,
// /time, /expand, /imports, /exports, /source, /sexp, /ast, /clif, /disasm,
// /mod commands. Formatting helpers for universal output format (spec section 1.1)
// are also here.

use std::io::Write;
use std::time::Instant;

use cranelisp_backend::display;
use cranelisp_types::{
    CranelispError, DefKind, MacroClauseInfo, MacroParam, ModuleEntry, ModuleFullPath,
    Sexp, TraitName, Type, TypeName,
};

use super::ReplSession;
use super::format_result_value;

// ── /sig ──────────────────────────────────────────────────────────────────────

/// Handle `/sig <name>` -- show type signature of a symbol.
pub(crate) fn handle_sig(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /sig <name>");
        return;
    }
    // Check builtin types first (not in symbol table)
    if Type::from_name(name).is_some() {
        let _ = writeln!(stdout, "{}", format_builtin_type_display(name, session));
        return;
    }
    let module = session.tc.current_module_path().clone();
    match session.tc.symbol_table().get(name) {
        Some(entry) => {
            let (resolved_entry, resolved_module) =
                resolve_entry_for_display(entry, &module, session);
            let display = format_entry_signature(resolved_entry, name, resolved_module, session);
            let _ = writeln!(stdout, "{display}");
        }
        None => {
            let _ = writeln!(stdout, "error: unknown symbol '{name}'");
        }
    }
}

// ── /doc ──────────────────────────────────────────────────────────────────────

/// Handle `/doc <name>` -- show docstring of a symbol (spec section 11.2.4).
pub(crate) fn handle_doc(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /doc <name>");
        return;
    }
    match session.tc.symbol_table().get(name) {
        Some(ModuleEntry::Macro { docstring, .. }) => {
            if let Some(doc) = docstring {
                let _ = writeln!(stdout, "{name}: \"{doc}\"");
            } else {
                let _ = writeln!(stdout, "{name}: no docstring");
            }
        }
        Some(ModuleEntry::Def { docstring, .. }) => {
            if let Some(doc) = docstring {
                let _ = writeln!(stdout, "{name}: \"{doc}\"");
            } else {
                let _ = writeln!(stdout, "{name}: no docstring");
            }
        }
        Some(ModuleEntry::TraitDecl { decl, .. }) => {
            if let Some(doc) = &decl.docstring {
                let _ = writeln!(stdout, "{name}: \"{doc}\"");
            } else {
                let _ = writeln!(stdout, "{name}: no docstring");
            }
        }
        Some(_) => {
            let _ = writeln!(stdout, "{name}: no docstring");
        }
        None => {
            let _ = writeln!(stdout, "error: unknown symbol '{name}'");
        }
    }
}

// ── /type ─────────────────────────────────────────────────────────────────────

/// Handle `/type <expr>` -- show type of expression without evaluating.
pub(crate) fn handle_type(session: &mut ReplSession, expr_src: &str, stdout: &mut impl Write) {
    if expr_src.is_empty() {
        let _ = writeln!(stdout, "usage: /type <expr>");
        return;
    }
    // Parse, build AST, typecheck -- but do NOT compile or execute.
    let snapshot = session.tc.snapshot();
    let result = typecheck_only(session, expr_src);
    // Always restore -- we don't want /type to have side effects.
    session.tc.restore(snapshot);
    match result {
        Ok(ty) => {
            let display = display::format_type_qualified(&ty, &session.type_modules);
            let _ = writeln!(stdout, ":{display}");
        }
        Err(e) => {
            let _ = writeln!(stdout, "error: {e}");
        }
    }
}

/// Parse, expand, and typecheck an expression without compiling or executing.
fn typecheck_only(session: &mut ReplSession, expr_src: &str) -> Result<Type, CranelispError> {
    let sexps = cranelisp_frontend::parse(expr_src)?;
    if sexps.is_empty() {
        return Err(CranelispError::ParseError {
            message: "empty expression".into(),
            span: cranelisp_types::Span::SYNTHETIC,
        });
    }
    let input = cranelisp_frontend::build_repl_input(&sexps[0], &mut session.expander)?;
    let check_result = session.tc.check_repl_input(&input)?;
    Ok(check_result.ty)
}

// ── /info ─────────────────────────────────────────────────────────────────────

/// Handle `/info <name>` -- show full details about a symbol (spec section 3.6).
pub(crate) fn handle_info(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /info <name>");
        return;
    }
    // Check builtin types first (not in symbol table)
    if Type::from_name(name).is_some() {
        let _ = writeln!(stdout, "{}", format_builtin_type_display(name, session));
        return;
    }
    let module = session.tc.current_module_path().clone();
    match session.tc.symbol_table().get(name) {
        Some(entry) => {
            let (resolved_entry, resolved_module) =
                resolve_entry_for_display(entry, &module, session);
            // Line 1: type signature (same as /sig).
            let sig = format_entry_signature(resolved_entry, name, resolved_module, session);
            let _ = writeln!(stdout, "{sig}");
            // Line 2: for functions, show code info.
            if !matches!(resolved_entry, ModuleEntry::Macro { .. } | ModuleEntry::TypeDef { .. } | ModuleEntry::TraitDecl { .. }) {
                if let Some(dc) = session.got_state.def_codegen.get(name) {
                    let size_str = dc
                        .code_size
                        .map(|s| format!("{s} bytes"))
                        .unwrap_or_else(|| "? bytes".to_string());
                    let time_str = dc
                        .compile_duration
                        .map(|d| format!("{}ms", d.as_millis()))
                        .unwrap_or_else(|| "?ms".to_string());
                    let _ = writeln!(stdout, "  {size_str}, {time_str}");
                }
            }
        }
        None => {
            let _ = writeln!(stdout, "error: unknown symbol '{name}'");
        }
    }
}

// ── /list ─────────────────────────────────────────────────────────────────────

/// Handle `/list [prefix]` -- list definitions in the current module (spec section 3.3).
///
/// Shows only symbols DEFINED in the current module. No imports, no special forms.
/// Categories: Modules, Macros, Traits, Types (incl constructors), Fns.
pub(crate) fn handle_list(session: &ReplSession, filter: &str, stdout: &mut impl Write) {
    let table = session.tc.symbol_table();

    let mut macros: Vec<String> = Vec::new();
    let mut traits: Vec<String> = Vec::new();
    let mut types: Vec<String> = Vec::new();
    let mut fns: Vec<String> = Vec::new();

    for (sym, entry) in table.all_symbols() {
        let name = sym.to_string();

        // Prefix match filter (case-insensitive)
        if !filter.is_empty()
            && !name.to_lowercase().starts_with(&filter.to_lowercase())
        {
            continue;
        }

        match entry {
            // Skip imports, reexports -- belong on /imports
            ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. } => {}
            // Types and their constructors in Types category
            ModuleEntry::TypeDef { .. } => {
                types.push(name);
            }
            ModuleEntry::Constructor { .. } => {
                types.push(name);
            }
            ModuleEntry::TraitDecl { .. } => {
                traits.push(name);
            }
            ModuleEntry::Macro { .. } => {
                macros.push(name);
            }
            ModuleEntry::Def { kind, .. } => {
                match kind.as_ref() {
                    // Skip special forms -- belong on /imports
                    DefKind::SpecialForm { .. } => {}
                    // Skip primitives -- belong in primitives module
                    DefKind::Primitive { .. } => {}
                    _ => {
                        fns.push(name);
                    }
                }
            }
            _ => {}
        }
    }

    macros.sort();
    traits.sort();
    types.sort();
    fns.sort();

    let has_any = !macros.is_empty() || !traits.is_empty()
        || !types.is_empty() || !fns.is_empty();

    if !has_any {
        let _ = writeln!(stdout, "(no definitions)");
        return;
    }

    // Category order: Modules, Macros, Traits, Types, Fns
    print_name_category("Macros", &macros, stdout);
    print_name_category("Traits", &traits, stdout);
    print_name_category("Types", &types, stdout);
    print_name_category("Fns", &fns, stdout);
}

// ── /time ─────────────────────────────────────────────────────────────────────

/// Handle `/time <expr>` -- evaluate with timing breakdown.
pub(crate) fn handle_time(
    session: &mut ReplSession,
    expr_src: &str,
) -> Result<String, CranelispError> {
    if expr_src.is_empty() {
        return Ok("usage: /time <expr>".to_string());
    }
    let total_start = Instant::now();
    let result = session.eval(expr_src)?;
    let total_elapsed = total_start.elapsed();

    // Compile time = total minus eval (function call) time.
    let compile_duration = total_elapsed.saturating_sub(result.eval_duration);
    let compile_ms = compile_duration.as_millis();
    let eval_ms = result.eval_duration.as_millis();

    // Format the result value.
    let display = if let Some(ref def_display) = result.definition_display {
        def_display.clone()
    } else {
        format_result_value(
            result.value,
            &result.ty,
            session.type_defs(),
            session.type_modules(),
        )
    };
    Ok(format!("{display} (compile: {compile_ms}ms, eval: {eval_ms}ms)"))
}

// ── /expand ───────────────────────────────────────────────────────────────────

/// Handle `/expand <form>` -- macro-expand a form without evaluating (spec section 11.1).
pub(crate) fn handle_expand(session: &mut ReplSession, form_src: &str, stdout: &mut impl Write) {
    if form_src.is_empty() {
        let _ = writeln!(stdout, "usage: /expand <form>");
        return;
    }
    match expand_form(session, form_src) {
        Ok(expanded) => {
            let _ = writeln!(stdout, "{expanded}");
        }
        Err(e) => {
            let _ = writeln!(stdout, "error: {e}");
        }
    }
}

/// Parse and expand a form through the session's macro expander.
///
/// Does not evaluate the result. Returns the expanded Sexp as a formatted string.
fn expand_form(session: &mut ReplSession, form_src: &str) -> Result<String, CranelispError> {
    let sexps = cranelisp_frontend::parse(form_src)?;
    if sexps.is_empty() {
        return Err(CranelispError::ParseError {
            message: "empty form".into(),
            span: cranelisp_types::Span::SYNTHETIC,
        });
    }
    let expanded = session.expander.expand_sexp(sexps.into_iter().next().ok_or_else(|| {
        CranelispError::ParseError {
            message: "empty form".into(),
            span: cranelisp_types::Span::SYNTHETIC,
        }
    })?)?;
    Ok(format_sexp(&expanded))
}

// ── /imports ──────────────────────────────────────────────────────────────────

/// Handle `/imports [module]` -- show imports in current module (spec section 3.4).
///
/// Unfiltered: organize by category (Special forms, Macros, Traits, Types, Fns).
/// Filtered: `/imports <module>` shows imports from that source module only,
/// organized as `From <module>:` groups with sorted names.
/// Names only -- no type signatures. Type the name for more detail.
pub(crate) fn handle_imports(session: &ReplSession, filter: &str, stdout: &mut impl Write) {
    let table = session.tc.symbol_table();

    if filter.is_empty() {
        // Unfiltered mode: organize by category (spec section 3.4)
        let mut special_forms: Vec<String> = Vec::new();
        let mut macros: Vec<String> = Vec::new();
        let mut traits: Vec<String> = Vec::new();
        let mut types: Vec<String> = Vec::new();
        let mut fns: Vec<String> = Vec::new();

        for (sym, entry) in table.all_symbols() {
            let name = sym.to_string();
            match entry {
                ModuleEntry::Def { kind, .. } => {
                    if let DefKind::SpecialForm { .. } = kind.as_ref() {
                        special_forms.push(name);
                    } else if matches!(kind.as_ref(), DefKind::Primitive { .. }) {
                        // Primitives are NOT shown in /imports (they're via module
                        // resolution fallback, not import).
                    } else {
                        // Skip locally-defined fns (not imports)
                    }
                }
                ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                    // Skip monomorphised variant names (e.g. add$Int+Int)
                    if name.contains('$') {
                        continue;
                    }
                    // Classify by looking up the source entry
                    let classification = classify_import(session, source);
                    match classification {
                        ImportClass::Macro => macros.push(name),
                        ImportClass::Trait => traits.push(name),
                        ImportClass::Type | ImportClass::Constructor => types.push(name),
                        ImportClass::Fn => fns.push(name),
                    }
                }
                _ => {} // TypeDef, TraitDecl, Constructor, Macro -- locally defined
            }
        }

        special_forms.sort();
        macros.sort();
        traits.sort();
        types.sort();
        fns.sort();

        // Special forms always present (spec section 3.4)
        print_name_category("Special forms", &special_forms, stdout);
        print_name_category("Macros", &macros, stdout);
        print_name_category("Traits", &traits, stdout);
        print_name_category("Types", &types, stdout);
        print_name_category("Fns", &fns, stdout);

        if special_forms.is_empty() && macros.is_empty() && traits.is_empty()
            && types.is_empty() && fns.is_empty()
        {
            // Shouldn't happen (special forms always present), but just in case
            let _ = writeln!(stdout, "(no imports)");
        }
    } else {
        // Filtered mode: `/imports <module>` -- show imports from that source module
        let mut names: Vec<String> = Vec::new();
        for (sym, entry) in table.all_symbols() {
            let source = match entry {
                ModuleEntry::Import { source } => source,
                ModuleEntry::Reexport { source } => source,
                _ => continue,
            };
            let name = sym.to_string();
            // Skip monomorphised variant names
            if name.contains('$') {
                continue;
            }
            if source.module.to_string() == filter {
                names.push(name);
            }
        }
        if names.is_empty() {
            // Silent re-prompt for no matches (spec section 3.4)
            return;
        }
        names.sort();
        print_name_category(&format!("From {filter}"), &names, stdout);
    }
}

// ── /exports ──────────────────────────────────────────────────────────────────

/// Handle `/exports <module>` -- list a module's public symbols (spec section 3.5).
///
/// Resolves the module, lists public symbols by category (names only).
/// Usage hint for no argument. Error for not-found module.
pub(crate) fn handle_exports(session: &ReplSession, arg: &str, stdout: &mut impl Write) {
    if arg.is_empty() {
        let _ = writeln!(stdout, "Usage: /exports <module-name>");
        return;
    }

    // Parse: first word is module name, rest is optional prefix filter
    let mut parts = arg.splitn(2, char::is_whitespace);
    let mod_name = parts.next().unwrap_or("");
    let prefix_filter = parts.next().unwrap_or("").trim();

    // Resolve module
    let module_path = match session.tc.resolve_module_by_name(mod_name) {
        Some(path) => path,
        None => {
            let _ = writeln!(stdout, "Module '{mod_name}' not found");
            return;
        }
    };

    // Get the module's symbol table
    let table = match session.tc.module_table(&module_path) {
        Some(t) => t,
        None => {
            let _ = writeln!(stdout, "Module '{mod_name}' not found");
            return;
        }
    };

    // Collect public symbols by category
    let mut macros: Vec<String> = Vec::new();
    let mut traits: Vec<String> = Vec::new();
    let mut types: Vec<String> = Vec::new();
    let mut fns: Vec<String> = Vec::new();

    for (sym, entry) in table.all_symbols() {
        // Skip imports/reexports -- those are the module's own imports, not exports
        if matches!(entry, ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. }) {
            continue;
        }
        // Skip non-public symbols
        if !entry.is_public() {
            continue;
        }
        let name = sym.to_string();
        // Skip monomorphised variant names
        if name.contains('$') {
            continue;
        }
        // Apply prefix filter if provided
        if !prefix_filter.is_empty()
            && !name.to_lowercase().starts_with(&prefix_filter.to_lowercase())
        {
            continue;
        }

        match entry {
            ModuleEntry::Macro { .. } => macros.push(name),
            ModuleEntry::TraitDecl { .. } => traits.push(name),
            ModuleEntry::TypeDef { .. } | ModuleEntry::Constructor { .. } => types.push(name),
            ModuleEntry::Def { kind, .. } => {
                if !matches!(kind.as_ref(), DefKind::SpecialForm { .. }) {
                    fns.push(name);
                }
            }
            _ => {}
        }
    }

    macros.sort();
    traits.sort();
    types.sort();
    fns.sort();

    let has_any = !macros.is_empty() || !traits.is_empty()
        || !types.is_empty() || !fns.is_empty();

    if !has_any {
        let _ = writeln!(stdout, "Module '{mod_name}' has no public symbols");
        return;
    }

    let _ = writeln!(stdout, "Module '{mod_name}':");
    print_name_category("Macros", &macros, stdout);
    print_name_category("Traits", &traits, stdout);
    print_name_category("Types", &types, stdout);
    print_name_category("Fns", &fns, stdout);
}

// ── /source /sexp /ast /clif /disasm ──────────────────────────────────────────

/// Handle `/source <name>` -- show original source text of a definition.
pub(crate) fn handle_source(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /source <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.source.is_some() => {
            let _ = writeln!(stdout, "; source for {name}");
            let _ = writeln!(stdout, "{}", dc.source.as_ref().unwrap());
        }
        _ => {
            let _ = writeln!(stdout, "error: no source available for '{name}'");
        }
    }
}

/// Handle `/sexp <name>` -- show the parsed S-expression of a definition.
pub(crate) fn handle_sexp(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /sexp <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.sexp.is_some() => {
            let _ = writeln!(stdout, "; sexp for {name}");
            let _ = writeln!(stdout, "{}", format_sexp(dc.sexp.as_ref().unwrap()));
        }
        _ => {
            let _ = writeln!(stdout, "error: no sexp available for '{name}'");
        }
    }
}

/// Handle `/ast <name>` -- show the AST (Defn) of a definition.
pub(crate) fn handle_ast(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /ast <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.defn.is_some() => {
            let _ = writeln!(stdout, "; ast for {name}");
            let _ = writeln!(stdout, "{:#?}", dc.defn.as_ref().unwrap());
        }
        _ => {
            let _ = writeln!(stdout, "error: no AST available for '{name}'");
        }
    }
}

/// Handle `/clif <name>` -- show the Cranelift IR of a definition.
pub(crate) fn handle_clif(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /clif <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.clif_ir.is_some() => {
            let _ = writeln!(stdout, "; clif ir for {name}");
            let _ = write!(stdout, "{}", dc.clif_ir.as_ref().unwrap());
        }
        _ => {
            let _ = writeln!(stdout, "error: no CLIF IR available for '{name}'");
        }
    }
}

/// Handle `/disasm <name>` -- show disassembled native code of a definition.
pub(crate) fn handle_disasm(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /disasm <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.disasm.is_some() => {
            let _ = writeln!(stdout, "; disasm for {name}");
            let _ = writeln!(stdout, "{}", dc.disasm.as_ref().unwrap());
        }
        _ => {
            let _ = writeln!(stdout, "error: no disassembly available for '{name}'");
        }
    }
}

// ── /mod ──────────────────────────────────────────────────────────────────────

/// Handle `/mod [name]` -- switch module namespace (spec section 8).
///
/// With no argument, switches to the `user` module (no output).
/// With an argument, switches to that module namespace (no output, creating it if needed).
pub(crate) fn handle_mod(session: &mut ReplSession, name: &str, _stdout: &mut impl Write) {
    let target = if name.is_empty() { "user" } else { name };
    let path = ModuleFullPath::from(target);
    session.tc.set_current_module(path);
}

// ── Formatting helpers ────────────────────────────────────────────────────────

/// Classification of an imported symbol for category-based display.
pub(super) enum ImportClass {
    Macro,
    Trait,
    Type,
    Constructor,
    Fn,
}

/// Classify an imported symbol by looking up the source entry.
///
/// Follows Import/Reexport chains to the ultimate definition (depth-limited).
pub(super) fn classify_import(session: &ReplSession, source: &cranelisp_types::FQSymbol) -> ImportClass {
    match resolve_to_definition(session, source) {
        Some(entry) => match entry {
            ModuleEntry::Macro { .. } => ImportClass::Macro,
            ModuleEntry::TraitDecl { .. } => ImportClass::Trait,
            ModuleEntry::TypeDef { .. } => ImportClass::Type,
            ModuleEntry::Constructor { .. } => ImportClass::Constructor,
            _ => ImportClass::Fn,
        },
        None => ImportClass::Fn, // Default: treat unknown as function
    }
}

/// Maximum depth for following Import/Reexport chains to prevent cycles.
const RESOLVE_DEPTH_LIMIT: usize = 10;

/// Follow Import/Reexport chains to find the ultimate definition entry.
///
/// Returns the concrete entry (Def, Macro, TypeDef, TraitDecl, Constructor)
/// or None if the chain is broken or exceeds the depth limit.
pub(super) fn resolve_to_definition<'a>(
    session: &'a ReplSession,
    source: &cranelisp_types::FQSymbol,
) -> Option<&'a ModuleEntry> {
    let mut current_module = source.module.clone();
    let mut current_name: String = source.symbol.to_string();
    for _ in 0..RESOLVE_DEPTH_LIMIT {
        let table = session.tc.module_table(&current_module)?;
        let entry = table.get(&current_name)?;
        match entry {
            ModuleEntry::Import { source: next } | ModuleEntry::Reexport { source: next } => {
                current_module = next.module.clone();
                current_name = next.symbol.to_string();
            }
            _ => return Some(entry),
        }
    }
    None // Depth limit exceeded (cycle or very deep chain)
}

/// Resolve an entry for display: if Import/Reexport, follow the chain to the
/// definition and return the resolved entry with its defining module.
///
/// Returns the original entry and module if not Import/Reexport or if
/// the chain cannot be resolved.
pub(super) fn resolve_entry_for_display<'a>(
    entry: &'a ModuleEntry,
    module: &'a ModuleFullPath,
    session: &'a ReplSession,
) -> (&'a ModuleEntry, &'a ModuleFullPath) {
    let source = match entry {
        ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => source,
        _ => return (entry, module),
    };
    // Follow the chain to the ultimate definition.
    let mut current_module = &source.module;
    let mut current_name: String = source.symbol.to_string();
    for _ in 0..RESOLVE_DEPTH_LIMIT {
        let table = match session.tc.module_table(current_module) {
            Some(t) => t,
            None => return (entry, module),
        };
        let resolved = match table.get(&current_name) {
            Some(e) => e,
            None => return (entry, module),
        };
        match resolved {
            ModuleEntry::Import { source: next } | ModuleEntry::Reexport { source: next } => {
                current_module = &next.module;
                current_name = next.symbol.to_string();
            }
            _ => return (resolved, current_module),
        }
    }
    (entry, module) // Depth limit exceeded -- return original
}

/// Format a module entry's type signature for /sig and /info display.
///
/// Uses universal output format (spec section 1.1).
pub(super) fn format_entry_signature(
    entry: &ModuleEntry,
    name: &str,
    module: &ModuleFullPath,
    session: &ReplSession,
) -> String {
    match entry {
        ModuleEntry::Def {
            scheme,
            kind,
            docstring,
            ..
        } => {
            if let DefKind::SpecialForm { description } = kind.as_ref() {
                return format_special_form_display(name, description);
            }
            let base = if !scheme.constraints.is_empty() {
                display::format_scheme_display(name, scheme, module, &session.type_modules)
            } else {
                let type_str = display::format_type_qualified(&scheme.ty, &session.type_modules);
                format!(":{type_str} {module}/{name}")
            };
            let classification = if matches!(kind.as_ref(), DefKind::Primitive { .. }) {
                "primitive"
            } else {
                "defn"
            };
            let base = format!("{base} ; {classification}");
            append_docstring_comment(base, docstring.as_deref())
        }
        ModuleEntry::Constructor {
            type_name, scheme, ..
        } => {
            let type_str = display::format_type_qualified(&scheme.ty, &session.type_modules);
            let tn = TypeName::from(type_name.0.as_str());
            let ctor_display = if let Some(info) = session.tc.type_def_registry().get(&tn) {
                display::format_ctor_display(&tn, name, info)
            } else {
                format!("{type_name}.{name}")
            };
            format!(":{type_str} {module}/{ctor_display} ; deftype")
        }
        ModuleEntry::TypeDef { .. } => {
            format_type_display_universal(name, module, session)
        }
        ModuleEntry::TraitDecl { decl, .. } => {
            format_trait_display_universal(name, decl.docstring.as_deref(), session)
        }
        ModuleEntry::Macro { clauses, docstring, .. } => {
            format_macro_display_universal(name, clauses, docstring.as_deref(), module)
        }
        _ => format!("{module}/{name}"),
    }
}

/// Format a single macro clause's parameter list.
///
/// Uses `& rest` syntax for variadic and bracket notation for destructuring.
fn format_macro_clause_params(clause: &MacroClauseInfo) -> String {
    let mut parts = Vec::new();
    for param in &clause.params {
        match param {
            MacroParam::Name(name) => {
                parts.push(name.to_string());
            }
            MacroParam::Bracket { fixed, rest } => {
                let mut inner = Vec::new();
                for f in fixed {
                    inner.push(f.to_string());
                }
                if let Some(r) = rest {
                    inner.push(format!("& {r}"));
                }
                parts.push(format!("[{}]", inner.join(" ")));
            }
        }
    }
    if let Some(rest) = &clause.rest_param {
        parts.push(format!("& {rest}"));
    }
    format!("[{}]", parts.join(" "))
}

/// Format a special form for display (spec section 4.1.5).
///
/// Produces a function-like signature with `; special form - description`.
pub(super) fn format_special_form_display(name: &str, description: &str) -> String {
    let type_sig = match name {
        "if" => ":(Fn [primitives/Bool a a] a)",
        "let" => ":(Fn [bindings body] a)",
        "fn" => ":(Fn [params body] function)",
        "defn" => ":(Fn [name params body] function)",
        "deftype" => ":(Fn [name ctors...] type)",
        "match" => ":(Fn [expr [pat body]...] a)",
        "defmacro" => ":(Fn [name params body] macro)",
        "deftrait" => ":(Fn [name methods...] trait)",
        "impl" => ":(Fn [trait type methods...] impl)",
        "import" => ":(Fn [module names] import)",
        "do" => ":(Fn [exprs...] a)",
        _ => "",
    };
    if type_sig.is_empty() {
        format!("{name} ; special form - {description}")
    } else {
        format!("{type_sig} {name} ; special form - {description}")
    }
}

/// Check if the trimmed input is a bare symbol name and return its display.
///
/// Handles special forms, primitive types, functions, constructors, traits,
/// and macros (spec section 4.1, section 11.4). Returns `Some(display_string)` if the
/// input matches a known symbol, `None` otherwise.
///
/// Universal output format (spec section 1.1):
///   `:Type {value|name} ; {classification} - {docstring}`
/// with optional related symbol sections for types, traits, and macros.
pub(crate) fn special_form_feedback(input: &str, session: &ReplSession) -> Option<String> {
    let trimmed = input.trim();
    // Must be a single bare identifier (no parens, no spaces, no brackets).
    if trimmed.contains(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']') {
        return None;
    }
    if trimmed.is_empty() {
        return None;
    }
    // Check primitive type names: Int, Bool, Float, String (spec section 4.1.3).
    // These live in the `primitives` synthetic module but are not bare names
    // in the user module's symbol table, so we check before the lookup.
    if Type::from_name(trimmed).is_some() {
        return Some(format_builtin_type_display(trimmed, session));
    }

    // Look up in the symbol table (spec section 4.1 -- bare symbol lookup).
    // Delegate to format_entry_signature which implements the universal format
    // for all symbol classes.
    let module = session.tc.current_module_path().clone();
    let entry = session.tc.symbol_table().get(trimmed)?;
    // For Import/Reexport entries, resolve through the chain to the definition.
    // This allows bare-symbol display for imported special forms, macros, etc.
    let (resolved_entry, resolved_module) =
        resolve_entry_for_display(entry, &module, session);
    // Nullary constructors (zero fields) have value semantics -- they evaluate
    // to a value, so let them pass through to eval instead of showing definition
    // metadata. Non-nullary constructors need arguments and can't be evaluated
    // bare, so they show introspection display (spec section 4.1).
    if let ModuleEntry::Constructor { info, .. } = resolved_entry
        && info.fields.is_empty()
    {
        return None;
    }
    Some(format_entry_signature(resolved_entry, trimmed, resolved_module, session))
}

/// Format a builtin type (Int, Bool, Float, String) for bare symbol lookup.
///
/// Shows `:primitives/Type ; type` with `; impl:` section listing traits
/// that have implementations for this type (spec section 4.1.3).
fn format_builtin_type_display(type_name: &str, session: &ReplSession) -> String {
    let tn = TypeName::from(type_name);
    let mut result = format!(":primitives/{type_name} ; type");
    let trait_names = session.tc.get_impls_for_type(&tn);
    if !trait_names.is_empty() {
        let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
        result.push_str(&format_related_section("impl", &names));
    }
    result
}

/// Format a user-defined type for bare symbol lookup (spec section 4.1.3).
///
/// Shows `:module/TypeName ; deftype` with `; match:` (constructors) and
/// `; impl:` (trait implementations) related symbol sections.
pub(super) fn format_type_display_universal(type_name: &str, module: &ModuleFullPath, session: &ReplSession) -> String {
    let mut result = format!(":{module}/{type_name} ; deftype");
    let tn = TypeName::from(type_name);
    // Related: constructors under `; match:`
    if let Some(ctors) = session.tc.get_type_constructors(&tn) {
        if !ctors.is_empty() {
            let names: Vec<&str> = ctors.iter().map(|c| c.name.as_ref()).collect();
            result.push_str(&format_related_section("match", &names));
        }
    }
    // Related: trait implementations under `; impl:`
    let trait_names = session.tc.get_impls_for_type(&tn);
    if !trait_names.is_empty() {
        let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
        result.push_str(&format_related_section("impl", &names));
    }
    result
}

/// Format a trait for bare symbol lookup (spec section 4.1.4).
///
/// Shows `:defining_module/TraitName ; deftrait` with `; defn:` (methods)
/// and `; impl:` (implementing types) related symbol sections.
pub(super) fn format_trait_display_universal(
    trait_name: &str,
    docstring: Option<&str>,
    session: &ReplSession,
) -> String {
    let defining_module = session.tc.defining_module_for(trait_name);
    let tn = TraitName::from(trait_name);
    let mut result = format!(":{defining_module}/{trait_name} ; deftrait");
    result = append_docstring_comment(result, docstring);
    // Related: methods under `; defn:`
    if let Some(methods) = session.tc.get_trait_methods(&tn) {
        if !methods.is_empty() {
            let names: Vec<&str> = methods.iter().map(|m| m.as_ref()).collect();
            result.push_str(&format_related_section("defn", &names));
        }
    }
    // Related: implementing types under `; impl:`
    let impl_types = session.tc.get_implementing_types(&tn);
    if !impl_types.is_empty() {
        let names: Vec<&str> = impl_types.iter().map(|t| t.as_ref()).collect();
        result.push_str(&format_related_section("impl", &names));
    }
    result
}

/// Format a macro for bare symbol lookup (spec section 4.1.6, section 11.4).
///
/// Shows `:module/name ; defmacro` with `; [params] -> Sexp` clause lines.
pub(super) fn format_macro_display_universal(
    name: &str,
    clauses: &[MacroClauseInfo],
    docstring: Option<&str>,
    module: &ModuleFullPath,
) -> String {
    let mut result = format!(":{module}/{name} ; defmacro");
    result = append_docstring_comment(result, docstring);
    for clause in clauses {
        let params = format_macro_clause_params(clause);
        result.push_str(&format!("\n; {params} -> Sexp"));
    }
    result
}

/// Format a related symbols section for universal output (spec section 1.1).
///
/// Produces `\n; {label}:\n;  name1 name2 ...` with names on one line.
fn format_related_section(label: &str, names: &[&str]) -> String {
    let mut result = format!("\n; {label}:");
    result.push_str(&format!("\n;  {}", names.join(" ")));
    result
}

/// Append the first line of a docstring as a ` ; comment` suffix.
///
/// Used by bare symbol display (spec section 4.1) to show a brief description
/// after the type/name display.
fn append_docstring_comment(base: String, docstring: Option<&str>) -> String {
    match docstring {
        Some(doc) if !doc.is_empty() => {
            let first_line = doc.lines().next().unwrap_or("");
            if first_line.is_empty() {
                base
            } else {
                format!("{base} ; {first_line}")
            }
        }
        _ => base,
    }
}

/// Print a category of names for `/list`, `/imports`, `/exports`.
///
/// Names are shown compactly: up to 6 per line for categories with 7+ names,
/// all on one line for smaller categories.
pub(super) fn print_name_category(label: &str, names: &[String], stdout: &mut impl Write) {
    if names.is_empty() {
        return;
    }
    let _ = writeln!(stdout, "{label}:");
    if names.len() < 7 {
        let _ = writeln!(stdout, "  {}", names.join(" "));
    } else {
        // Compact layout: 6 names per line
        for chunk in names.chunks(6) {
            let _ = writeln!(stdout, "  {}", chunk.join(" "));
        }
    }
}

/// Format an S-expression as a readable string.
///
/// Produces valid S-expression syntax: symbols, integers, floats, booleans,
/// strings (quoted), lists (parenthesized), and brackets (square).
pub(super) fn format_sexp(sexp: &Sexp) -> String {
    match sexp {
        Sexp::Symbol(name, _) => name.clone(),
        Sexp::Int(n, _) => format!("{n}"),
        Sexp::Float(v, _) => {
            let s = format!("{v}");
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        Sexp::Bool(b, _) => format!("{b}"),
        Sexp::Str(s, _) => format!("\"{s}\""),
        Sexp::List(children, _) => {
            let parts: Vec<String> = children.iter().map(format_sexp).collect();
            format!("({})", parts.join(" "))
        }
        Sexp::Bracket(children, _) => {
            let parts: Vec<String> = children.iter().map(format_sexp).collect();
            format!("[{}]", parts.join(" "))
        }
    }
}
