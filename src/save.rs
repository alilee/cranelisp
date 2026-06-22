// Session persistence: source regeneration and atomic write.
//
// Implements repl/spec.md §15 and design/int/session-persistence.md.
// Regenerates the backing .cl file for the current module from the
// symbol table after each definition.
//
// Sprint 58 Step 5a (Decision 33): the structural decls
// (imports/exports/platforms/submodules) live as fields on `SymbolTable`
// itself. The transitional `ModuleStructure` parallel store on
// `SharedState.module_structures` dissolves; this module reads everything
// from `SymbolTable`.

use std::collections::HashSet;
use std::io::Write;
use std::path::Path;

use cranelisp_types::{
    ExportSpec, FQSymbol, ImportNames, ImportSpec, ModDecl, ModuleEntry,
    ModuleFullPath, PlatformSpec, Sexp,
};

use dashmap::DashMap;

use crate::session_v4::Introspection;

// ---------------------------------------------------------------------------
// Regeneration role gate (FIXME 0343)
// ---------------------------------------------------------------------------

/// Pure predicate: MAY the entry-module persistence path overwrite this
/// module's backing `.cl` with regenerated source?
///
/// Returns `false` — i.e. PRESERVE the file verbatim, do NOT regenerate —
/// when the module declares a submodule that still carries an inline body
/// (`ModDecl.inline_body == Some`). Such a parent's backing file holds an
/// authored `(mod child form…)` block whose definitions live in the CHILD's
/// symbol table, NOT the parent's; regenerating from the parent table alone
/// would emit a bare `(mod child)` and silently DROP the entire submodule body
/// from disk — a data-corruption defect (FIXME 0343, same class as 0217).
///
/// In REPL mode the inline body is deliberately NOT extracted to a bare
/// reference (`process_form::handle_mod` runs the extraction rewrite only in
/// batch mode), so the in-memory `ModDecl` keeps its `inline_body` — the signal
/// this gate keys on. A manually-created / already-extracted submodule carries
/// `inline_body: None`, so an ordinary `(mod util)`-bearing module regenerates
/// normally (the child lives in its own file the regen never touches).
///
/// Extracted as a pure fn (no `&self`, no FS) so the role gate is unit-testable
/// (`src/CLAUDE.md` testability discipline; mirrors `splice_inline_mod_to_bare`
/// / `layout_hash_gate`).
pub(crate) fn should_regenerate(symbol_table: &crate::code::SessionSymbolTable) -> bool {
    !symbol_table
        .submodules
        .iter()
        .any(|decl| decl.inline_body.is_some())
}

// ---------------------------------------------------------------------------
// Source regeneration — pure function
// ---------------------------------------------------------------------------

/// Generate complete module source from the module's `SymbolTable`.
///
/// Pure function: reads data, returns source text. Sections appear in
/// the order specified by design/int/session-persistence.md §1.3:
///   1. mod decls
///   2. platform decls
///   3. imports (merged, prelude filtered)
///   4. exports (merged)
///   5. traits (alphabetical)
///   6. types (alphabetical)
///   7. impls (from TraitImpl entries)
///   8. fns and macros (dependency-sorted)
///
/// Sprint 58 Step 5a: structural decls read directly from
/// `symbol_table.{submodules, platforms, imports, exports}`. The implicit
/// prelude `(import [prelude [*]])` is suppressed by `generate_imports`
/// itself — `imports` records only user-authored forms (CP3 / option (b),
/// see `design/int/symbol-table-cache.md` §3) but the filter remains as a
/// belt-and-braces guard.
pub fn generate_module_source(
    symbol_table: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> String {
    let mut sections = Vec::new();

    // 0. Module preamble (spec §8.16.5) — the leading `;;` comment block at the
    //    file head, ABOVE the first form. Re-emitted verbatim from
    //    `symbol_table.module_preamble` (captured on load by
    //    `cranelisp_frontend::capture_module_preamble`). The capture/re-emit
    //    pair is INVERSE on the canonical `;;`-and-one-space form (§8.16.3 /
    //    §6.3 inverse-pair invariant): capture stripped `;;` + one space, so
    //    re-emit prefixes each line with `;; ` (one space) — an unedited
    //    preamble round-trips byte-identically. `None` ⇒ no section-0 block.
    if let Some(preamble) = &symbol_table.module_preamble {
        let block = generate_preamble(preamble);
        if !block.is_empty() {
            sections.push(block);
        }
    }

    // 1. Module declarations
    let mod_section = generate_mod_decls(&symbol_table.submodules);
    if !mod_section.is_empty() {
        sections.push(mod_section);
    }

    // 2. Platform declarations
    let platform_section = generate_platforms(&symbol_table.platforms);
    if !platform_section.is_empty() {
        sections.push(platform_section);
    }

    // 3. Imports (merged, prelude filtered)
    let import_section = generate_imports(&symbol_table.imports);
    if !import_section.is_empty() {
        sections.push(import_section);
    }

    // 4. Exports (merged)
    let export_section = generate_exports(&symbol_table.exports);
    if !export_section.is_empty() {
        sections.push(export_section);
    }

    // 5. Trait declarations (alphabetical)
    let trait_section = generate_traits(symbol_table, introspection, module_path);
    if !trait_section.is_empty() {
        sections.push(trait_section);
    }

    // 6. Type definitions (alphabetical)
    let type_section = generate_types(symbol_table, introspection, module_path);
    if !type_section.is_empty() {
        sections.push(type_section);
    }

    // 7. Trait implementations
    let impl_section = generate_impls(symbol_table);
    if !impl_section.is_empty() {
        sections.push(impl_section);
    }

    // 8. Functions and macros (dependency-sorted)
    let fn_section = generate_fns_and_macros(symbol_table, introspection, module_path);
    if !fn_section.is_empty() {
        sections.push(fn_section);
    }

    let mut result = sections.join("\n\n");
    if !result.is_empty() {
        result.push('\n');
    }
    result
}

// ---------------------------------------------------------------------------
// Colon-annotation-aware rendering (FIXME 0423 secondary symptom)
// ---------------------------------------------------------------------------

/// Render a definition `Sexp` for source-regeneration, emitting compound type
/// annotations as `:(Option String)` (NO space after `:`), not `: (Option
/// String)`.
///
/// FIXME 0423 secondary symptom + `memory/annotation-reader-macro-binds-following-form`:
/// the reader represents a COMPOUND annotation `:(Option String)` as two sibling
/// forms — a bare `Sexp::Symbol(":")` immediately followed by the type form. The
/// generic `Sexp::format_indented` joins all siblings with a single space, so it
/// emits `: (Option String)`, inserting a space the reader semantics forbid
/// (`:` binds the IMMEDIATELY-following form with no separator). A simple-symbol
/// annotation (`:Int`, `:primitives/Int`) is a single `Sexp::Symbol(":Int")`
/// and already round-trips correctly — only the bare-`:` + following-form case
/// needs the space suppressed.
///
/// This regen-local renderer mirrors `format_indented`'s line-fitting but, when
/// a child is the bare colon-annotation symbol `":"`, attaches the FOLLOWING
/// child with no separating space (flat or indented). It is the regen path's
/// renderer; the generic `format_indented` is left untouched (it is
/// `cranelisp-types`-owned; the colon-binding round-trip is a regen concern).
fn render_decl_sexp(sexp: &Sexp) -> String {
    render_decl_sexp_indented(sexp, 0)
}

/// `true` iff `s` is the bare colon-annotation marker symbol (`":"`), the
/// reader's representation of a `:`-prefix on a COMPOUND (`(…)`) type form.
fn is_bare_colon(s: &Sexp) -> bool {
    matches!(s, Sexp::Symbol(name, _) if name == ":")
}

/// Flat (single-line) render with colon-binding suppression of the separator.
fn render_decl_flat(sexp: &Sexp) -> String {
    match sexp {
        Sexp::List(children, _) => format!("({})", render_children_flat(children)),
        Sexp::Bracket(children, _) => format!("[{}]", render_children_flat(children)),
        // Leaves + simple `:Int` symbols + comments render as the generic flat.
        _ => sexp.format_flat(),
    }
}

/// Join children flat, suppressing the space AFTER a bare `:` colon marker so it
/// binds the following form (`: (Option …)` → `:(Option …)`).
fn render_children_flat(children: &[Sexp]) -> String {
    let mut out = String::new();
    let mut suppress_sep = false;
    for (i, child) in children.iter().enumerate() {
        if i > 0 && !suppress_sep {
            out.push(' ');
        }
        out.push_str(&render_decl_flat(child));
        suppress_sep = is_bare_colon(child);
    }
    out
}

/// Indented render mirroring `Sexp::format_indented`, but colon-binding aware.
fn render_decl_sexp_indented(sexp: &Sexp, indent: usize) -> String {
    if matches!(sexp, Sexp::Comment(_, _)) {
        return sexp.format_flat();
    }
    let flat = render_decl_flat(sexp);
    if flat.len() <= 60 {
        return flat;
    }
    let (open, close, child_indent) = match sexp {
        Sexp::List(children, _) if !children.is_empty() => ('(', ')', indent + 2),
        Sexp::Bracket(children, _) if !children.is_empty() => ('[', ']', indent + 1),
        _ => return flat,
    };
    let children = match sexp {
        Sexp::List(c, _) | Sexp::Bracket(c, _) => c,
        _ => unreachable!("guarded above"),
    };
    let pad = " ".repeat(child_indent);

    // Greedily fit short items on the first line (like format_indented), but
    // when an item is the bare `:` colon marker, attach the NEXT item to it
    // with no separating space so the annotation binds its following form.
    let mut first_line = format!("{}{}", open, render_decl_flat(&children[0]));
    let mut rest_start = 1;
    let mut prev_colon = is_bare_colon(&children[0]);
    while rest_start < children.len() {
        let next_flat = render_decl_flat(&children[rest_start]);
        let sep_len = if prev_colon { 0 } else { 1 };
        if first_line.len() + sep_len + next_flat.len() <= 60 {
            if !prev_colon {
                first_line.push(' ');
            }
            first_line.push_str(&next_flat);
            prev_colon = is_bare_colon(&children[rest_start]);
            rest_start += 1;
        } else {
            break;
        }
    }
    if rest_start >= children.len() {
        first_line.push(close);
        return first_line;
    }
    let mut result = first_line;
    let mut idx = rest_start;
    while idx < children.len() {
        let child_str = render_decl_sexp_indented(&children[idx], child_indent);
        // A colon marker that lands at a line break binds the following form on
        // the SAME line (`:(Option …)`), never `:`-on-its-own-line.
        if is_bare_colon(&children[idx]) && idx + 1 < children.len() {
            let next_str = render_decl_flat(&children[idx + 1]);
            result.push('\n');
            result.push_str(&pad);
            result.push_str(&child_str);
            result.push_str(&next_str);
            idx += 2;
        } else {
            result.push('\n');
            result.push_str(&pad);
            result.push_str(&child_str);
            idx += 1;
        }
    }
    result.push(close);
    result
}

// ---------------------------------------------------------------------------
// Section generators
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Module-preamble wiring (frontend → int seam; design/frontend/module-preamble.md §5)
// ---------------------------------------------------------------------------

/// Capture the leading-comment-block module preamble from `source` (via
/// `cranelisp_frontend::capture_module_preamble`) and write it onto the live
/// `SymbolTable.module_preamble` for `module`, ensuring the table exists.
///
/// The frontend hands off a pure `&str -> Option<String>`; int threads it onto
/// the right module's table at each fresh-source load site (§5). This is the
/// "one call + one field assignment per load site" wiring — orthogonal to
/// `extract_module_declarations` (the structural-decl peel is left untouched).
///
/// Cache restore does NOT call this: a cache-restored module carries its
/// preamble through serde (`#[serde(default)]`, schema 8→9), so re-capturing on
/// a cache hit would be redundant. Capture runs only on a fresh source parse.
///
/// The live table persists across the typecheck commit
/// (`worker::commit_staging_to_live` only writes `symbols`, never
/// `module_preamble`), so setting the field here survives codegen.
pub(crate) fn apply_module_preamble(
    symbol_tables: &DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    source: &str,
) {
    let preamble = cranelisp_frontend::capture_module_preamble(source);
    cranelisp_types::ensure_module_exists(symbol_tables, module);
    if let Some(mut st) = symbol_tables.get_mut(module) {
        st.module_preamble = preamble;
    }
}

/// Re-emit a captured module preamble as the leading `;;` comment block
/// (spec §8.16.5 section-0). Each `\n`-split line is prefixed with `;; ` (one
/// space) and joined with `\n` — the EXACT inverse of `capture_module_preamble`'s
/// strip (marker + one space, §8.16.2). A blank preamble line (`""`) re-marks as
/// a bare `;;` (no trailing space), preserving the inverse-pair invariant so an
/// unedited preamble round-trips byte-identically (§6.3).
fn generate_preamble(text: &str) -> String {
    text.split('\n')
        .map(|line| {
            if line.is_empty() {
                ";;".to_string()
            } else {
                format!(";; {line}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn generate_mod_decls(decls: &[ModDecl]) -> String {
    decls
        .iter()
        .map(|decl| {
            let keyword = if decl.visibility == cranelisp_types::Visibility::Private {
                "mod-"
            } else {
                "mod"
            };
            format!("({} {})", keyword, decl.name)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn generate_platforms(specs: &[PlatformSpec]) -> String {
    let mut platforms: Vec<String> = specs
        .iter()
        .map(|spec| format!("(platform {})", spec.name))
        .collect();
    platforms.sort();
    platforms.dedup();
    platforms.join("\n")
}

/// Merge and generate a single `(import [...])` form.
/// Filters out the implicit prelude import.
fn generate_imports(specs: &[ImportSpec]) -> String {
    // Filter out implicit prelude import
    let filtered: Vec<&ImportSpec> = specs
        .iter()
        .filter(|s| {
            !(s.module_path == "prelude" && s.names == ImportNames::Glob && s.alias.is_none())
        })
        .collect();

    if filtered.is_empty() {
        return String::new();
    }

    // Group by module_path, merging names
    let mut groups: Vec<(String, Option<String>, ImportNames)> = Vec::new();
    for spec in &filtered {
        let mod_path = spec.module_path.to_string();
        let alias = spec.alias.as_ref().map(|a| a.to_string());
        if let Some(existing) = groups.iter_mut().find(|(path, _, _)| *path == mod_path) {
            // Merge: Glob wins over Specific
            match (&existing.2, &spec.names) {
                (ImportNames::Glob, _) => {}
                (_, ImportNames::Glob) => existing.2 = ImportNames::Glob,
                (ImportNames::Specific(existing_names), ImportNames::Specific(new_names)) => {
                    let mut merged = existing_names.clone();
                    for name in new_names {
                        if !merged.contains(name) {
                            merged.push(name.clone());
                        }
                    }
                    existing.2 = ImportNames::Specific(merged);
                }
                _ => {}
            }
        } else {
            groups.push((mod_path, alias, spec.names.clone()));
        }
    }

    let mut parts = Vec::new();
    for (module_path, alias, names) in &groups {
        let mod_part = match alias {
            Some(a) => format!("({} {})", module_path, a),
            None => module_path.clone(),
        };
        let names_part = match names {
            ImportNames::Glob => "[*]".to_string(),
            ImportNames::Specific(names) => {
                let name_strs: Vec<&str> = names.iter().map(|n| n.as_ref()).collect();
                format!("[{}]", name_strs.join(" "))
            }
            ImportNames::MemberGlob(parent) => format!("[{}.*]", parent),
            ImportNames::None => "[]".to_string(),
        };
        parts.push(format!("{} {}", mod_part, names_part));
    }

    format!("(import [{}])", parts.join(" "))
}

fn generate_exports(specs: &[ExportSpec]) -> String {
    if specs.is_empty() {
        return String::new();
    }

    let mut parts = Vec::new();
    for spec in specs {
        let names_part = match &spec.names {
            ImportNames::Glob => "[*]".to_string(),
            ImportNames::Specific(names) => {
                let name_strs: Vec<&str> = names.iter().map(|n| n.as_ref()).collect();
                format!("[{}]", name_strs.join(" "))
            }
            ImportNames::MemberGlob(parent) => format!("[{}.*]", parent),
            ImportNames::None => "[]".to_string(),
        };
        parts.push(format!("{} {}", spec.module_path, names_part));
    }

    format!("(export [{}])", parts.join(" "))
}

/// Look up the canonical `sexp` for a symbol from the Introspection DashMap
/// (per Decision 41: `Introspection` is the single store for source/sexp/
/// expanded/clif_ir/code_size across all `DefKind` variants and
/// `ModuleEntry::{TypeDef, TraitDecl}`). Returns `None` for cache-loaded
/// modules whose Introspection has not been rehydrated — tracked at
/// FIXME 0220 (lazy re-read on demand); the symmetric None-skip is the
/// correct behaviour at this site.
fn introspection_sexp(
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
    name: &cranelisp_types::Symbol,
) -> Option<Sexp> {
    let fq = FQSymbol {
        module: module_path.clone(),
        symbol: name.clone(),
    };
    introspection
        .and_then(|m| m.get(&fq))
        .and_then(|intro| intro.sexp.clone())
}

fn generate_traits(
    st: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> String {
    let mut items: Vec<(String, String)> = Vec::new();
    for (name, entry) in st.all_symbols() {
        if let ModuleEntry::TraitDecl { .. } = entry
            && let Some(sexp) = introspection_sexp(introspection, module_path, name)
        {
            items.push((name.to_string(), render_decl_sexp(&sexp)));
        }
    }
    items.sort_by(|a, b| a.0.cmp(&b.0));
    items
        .into_iter()
        .map(|(_, text)| text)
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn generate_types(
    st: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> String {
    let mut items: Vec<(String, String)> = Vec::new();
    for (name, entry) in st.all_symbols() {
        if let ModuleEntry::TypeDef { .. } = entry
            && let Some(sexp) = introspection_sexp(introspection, module_path, name)
        {
            items.push((name.to_string(), render_decl_sexp(&sexp)));
        }
    }
    items.sort_by(|a, b| a.0.cmp(&b.0));
    items
        .into_iter()
        .map(|(_, text)| text)
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// Generate trait implementations. Uses sexp from TraitImpl entries
/// on the symbol table (if they have sexp fields). Falls back to
/// introspection for impl method sources.
fn generate_impls(st: &crate::code::SessionSymbolTable) -> String {
    // TraitImpl entries currently don't have an sexp field (see §2.1 gap).
    // For now, skip impl regeneration — impls will need the sexp field
    // added to ModuleEntry::TraitImpl as a prerequisite (design §9.1).
    // This allows basic persistence (defn, deftype, import) to work.
    let _ = st;
    String::new()
}

fn generate_fns_and_macros(
    st: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> String {
    // Partition into macros and non-macro fns. Macros MUST be emitted BEFORE
    // the functions that use them (S77 W-MacroTrait, FIXME 0299): defmacro-
    // before-use is normative (`macro-availability-model.md` §0.2), and the
    // regenerated file must be round-trip-safe (§0.3 — a cached REPL restart
    // recompiles the regenerated `user.cl` under the SAME availability rules
    // the live session used). The callee-list `dependency_sort` does NOT model
    // the macro-use edge (a macro call is not a `callees()` entry), so without
    // this partition `(defn main [] (twice 21))` could be emitted before
    // `(defmacro twice …)`, and the restart would reject `twice` as a forward
    // reference. Per the locked model a macro depends only on PRIOR modules +
    // other macros (never a same-module non-macro def), so emitting all macros
    // first is always valid; functions then see every macro defined above them.
    let mut macro_items: Vec<(String, Sexp)> = Vec::new();
    let mut fn_items: Vec<(String, Sexp)> = Vec::new();

    for (name, entry) in st.all_symbols() {
        // Skip mangled names (impl methods like `show$Int`, macro clause
        // variants like `m$clause-0`)
        if name.contains('$') {
            continue;
        }
        // Predicate: include both UserFn and Macro Def entries for
        // regeneration; skip primitives, constructors, platform effects,
        // overloaded base entries, etc. Per FIXME 0219 — macros surface
        // through the same `ModuleEntry::Def` arm symmetric with UserFn.
        // For macros, capture the symbol-table `macro_sexp` (D1 ruling §6) as a
        // fallback source: a cache-restored-then-REPL-edited `defmacro` has no
        // introspection record (introspection is REPL-only and absent on cache
        // restore), but `macro_sexp` round-trips the cache — without this
        // fallback `regenerate_backing_file` would silently DROP the macro from
        // the regenerated `.cl`, breaking a cached REPL restart that uses it.
        let (is_macro, macro_table_sexp) = match entry {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                cranelisp_types::DefKind::Macro { macro_sexp, .. } => {
                    (true, Some(macro_sexp.clone()))
                }
                cranelisp_types::DefKind::UserFn { .. } => (false, None),
                _ => continue,
            },
            _ => continue,
        };
        // Prefer the introspection record (carries the verbatim REPL input text
        // when present); fall back to the symbol-table `macro_sexp` for macros.
        let sexp = introspection_sexp(introspection, module_path, name)
            .or(macro_table_sexp);
        if let Some(sexp) = sexp {
            if is_macro {
                macro_items.push((name.to_string(), sexp));
            } else {
                fn_items.push((name.to_string(), sexp));
            }
        }
    }

    // Dependency-sort each section independently (macro→macro and fn→fn
    // intra-section edges still matter), then concatenate macros-first.
    let macros_sorted = dependency_sort(macro_items, st);
    let fns_sorted = dependency_sort(fn_items, st);
    macros_sorted
        .into_iter()
        .chain(fns_sorted)
        .map(|(_, sexp)| render_decl_sexp(&sexp))
        .collect::<Vec<_>>()
        .join("\n\n")
}

// ---------------------------------------------------------------------------
// Cache-hit introspection rehydration (FIXME 0220 — /arch ruling S81)
// ---------------------------------------------------------------------------

/// Does this top-level form define `name`?
///
/// Recognises the defining special forms `(defn name …)`, `(defmacro name …)`,
/// `(deftype name …)`, `(deftrait name …)` — the forms `generate_*` emits and
/// therefore the forms a re-read of the backing `.cl` must be able to map back
/// to a symbol. Returns `false` for structural forms (`import`/`export`/`mod`/
/// `platform`) which define no named symbol in the symbol table.
pub(crate) fn sexp_defines_symbol(sexp: &Sexp, name: &str) -> bool {
    if let Sexp::List(items, _) = sexp
        && items.len() >= 2
        && let Sexp::Symbol(head, _) = &items[0]
        && matches!(head.as_str(), "defn" | "defmacro" | "deftype" | "deftrait")
        && let Sexp::Symbol(defined, _) = &items[1]
    {
        return defined.as_str() == name;
    }
    false
}

/// Lazy on-demand introspection rehydration for cache-loaded symbols
/// (FIXME 0220, /arch ruling S81 item 3 — the non-macro `.cl`-regen gap).
///
/// A module restored from the on-disk compile cache populates its
/// `SymbolTable` but NOT the REPL-only `Introspection` DashMap (introspection
/// is REPL-only by design and never serialized into the cache — see
/// `memory/introspection-repl-only-principle.md`). Macros survive regeneration
/// because their source rides `DefKind::Macro.macro_sexp` (cache-serialized),
/// but a cache-restored regular `UserFn` with no introspection record was
/// silently DROPPED from the regenerated `.cl` by `generate_fns_and_macros`
/// (its `introspection_sexp(..).or(macro_table_sexp)` covers macros only).
///
/// This re-reads + re-parses the backing `.cl` (always present — it is the
/// cache key), locates each top-level form that defines a `UserFn` whose
/// `Introspection.sexp` is absent, and populates the record from the parsed
/// form. Content-fresh at the moment of need; the read-only REPL session pays
/// nothing. `frontend` owns the parse; file-IO + populate is int's (one
/// private path). Returns the number of records rehydrated.
pub(crate) fn rehydrate_userfn_introspection_from_source(
    st: &crate::code::SessionSymbolTable,
    introspection: &DashMap<FQSymbol, Introspection>,
    module_path: &ModuleFullPath,
    backing_source: &str,
) -> usize {
    // Which UserFns lack an introspection sexp? (Macros are handled by the
    // macro_sexp fallback and need no rehydration; other DefKinds are not
    // regenerated as fn/macro source.)
    let mut missing: Vec<cranelisp_types::Symbol> = Vec::new();
    for (name, entry) in st.all_symbols() {
        if name.contains('$') {
            continue;
        }
        let is_userfn = matches!(
            entry,
            ModuleEntry::Def { kind, .. }
                if matches!(kind.as_ref(), cranelisp_types::DefKind::UserFn { .. })
        );
        if !is_userfn {
            continue;
        }
        let fq = FQSymbol {
            module: module_path.clone(),
            symbol: name.clone(),
        };
        let has_sexp = introspection
            .get(&fq)
            .map(|i| i.sexp.is_some())
            .unwrap_or(false);
        if !has_sexp {
            missing.push(name.clone());
        }
    }

    if missing.is_empty() {
        return 0;
    }

    let sexps = match cranelisp_frontend::parse(backing_source) {
        Ok(s) => s,
        Err(_) => return 0,
    };

    let mut rehydrated = 0;
    for name in &missing {
        if let Some(sexp) = sexps.iter().find(|s| sexp_defines_symbol(s, name.as_ref())) {
            let fq = FQSymbol {
                module: module_path.clone(),
                symbol: name.clone(),
            };
            let mut entry = introspection.entry(fq).or_default();
            entry.sexp = Some(sexp.clone());
            if entry.source.is_none() {
                entry.source = Some(crate::pretty::pretty_print(sexp));
            }
            rehydrated += 1;
        }
    }
    rehydrated
}

// ---------------------------------------------------------------------------
// Dependency sorting (Kahn's topological sort)
// ---------------------------------------------------------------------------

/// Sort functions/macros by dependency order using callee lists from the
/// symbol table (Decision 21). Items with no intra-module deps appear first.
/// Cycles are broken alphabetically.
fn dependency_sort(items: Vec<(String, Sexp)>, st: &crate::code::SessionSymbolTable) -> Vec<(String, Sexp)> {
    if items.len() <= 1 {
        return items;
    }

    let names: HashSet<&str> = items.iter().map(|(n, _)| n.as_str()).collect();

    // Build adjacency from callee lists (intra-module only)
    let mut deps: std::collections::HashMap<&str, HashSet<&str>> = std::collections::HashMap::new();
    for (name, _) in &items {
        let mut item_deps = HashSet::new();
        if let Some(entry) = st.get(name) {
            for callee in entry.callees() {
                let callee_name = callee.symbol.as_ref();
                if names.contains(callee_name)
                    && callee_name != name.as_str()
                    && callee.module == st.path
                {
                    item_deps.insert(callee_name);
                }
            }
        }
        deps.insert(name.as_str(), item_deps);
    }

    // Kahn's algorithm
    let mut in_degree: std::collections::HashMap<&str, usize> =
        std::collections::HashMap::new();
    let mut dependents: std::collections::HashMap<&str, Vec<&str>> =
        std::collections::HashMap::new();
    for (name, _) in &items {
        in_degree.entry(name.as_str()).or_insert(0);
    }
    for (name, item_deps) in &deps {
        for dep in item_deps {
            dependents.entry(*dep).or_default().push(*name);
            *in_degree.entry(*name).or_insert(0) += 1;
        }
    }

    let mut queue: Vec<&str> = in_degree
        .iter()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(name, _)| *name)
        .collect();
    queue.sort_by(|a, b| b.cmp(a)); // reverse so pop() gives smallest

    let mut order: Vec<String> = Vec::new();
    while let Some(name) = queue.pop() {
        order.push(name.to_string());
        if let Some(dep_list) = dependents.get(name) {
            for dep_name in dep_list {
                if let Some(deg) = in_degree.get_mut(dep_name) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push(*dep_name);
                        queue.sort_by(|a, b| b.cmp(a));
                    }
                }
            }
        }
    }

    // Remaining items (cycles) added alphabetically
    let ordered_set: HashSet<&str> = order.iter().map(|s| s.as_str()).collect();
    let mut remaining: Vec<String> = items
        .iter()
        .filter(|(n, _)| !ordered_set.contains(n.as_str()))
        .map(|(n, _)| n.clone())
        .collect();
    remaining.sort();
    order.extend(remaining);

    // Reorder items according to order
    let item_map: std::collections::HashMap<String, Sexp> = items.into_iter().collect();
    order
        .into_iter()
        .filter_map(|name| item_map.get(&name).map(|sexp| (name, sexp.clone())))
        .collect()
}

// ---------------------------------------------------------------------------
// Atomic write
// ---------------------------------------------------------------------------

/// Write content to a file atomically (temp file + rename).
/// The temp file is placed in the same directory to ensure atomic rename.
pub fn atomic_write(path: &Path, content: &str) -> std::io::Result<()> {
    let dir = path.parent().unwrap_or_else(|| Path::new("."));
    if !dir.exists() {
        std::fs::create_dir_all(dir)?;
    }
    let tmp_path = path.with_extension("cl.tmp");
    let mut file = std::fs::File::create(&tmp_path)?;
    file.write_all(content.as_bytes())?;
    file.flush()?;
    // fsync for durability
    file.sync_all()?;
    drop(file);
    std::fs::rename(&tmp_path, path)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Span;

    #[test]
    fn merge_imports_filters_prelude() {
        let specs = vec![ImportSpec {
            module_path: "prelude".into(),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_imports(&specs), "");
    }

    #[test]
    fn merge_imports_specific() {
        let specs = vec![ImportSpec {
            module_path: "core".into(),
            alias: None,
            names: ImportNames::Specific(vec!["foo".into(), "bar".into()]),
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_imports(&specs), "(import [core [foo bar]])");
    }

    #[test]
    fn merge_imports_glob_wins() {
        let specs = vec![
            ImportSpec {
                module_path: "core".into(),
                alias: None,
                names: ImportNames::Specific(vec!["foo".into()]),
                span: Span::SYNTHETIC,
            },
            ImportSpec {
                module_path: "core".into(),
                alias: None,
                names: ImportNames::Glob,
                span: Span::SYNTHETIC,
            },
        ];
        assert_eq!(generate_imports(&specs), "(import [core [*]])");
    }

    #[test]
    fn generate_exports_empty() {
        assert_eq!(generate_exports(&[]), "");
    }

    #[test]
    fn generate_mod_decls_basic() {
        let decls = vec![ModDecl {
            name: "helper".into(),
            visibility: cranelisp_types::Visibility::Public,
            inline_body: None,
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_mod_decls(&decls), "(mod helper)");
    }

    // FIXME 0220 (/arch ruling S81, item 3): a cache-restored regular UserFn
    // with no REPL Introspection record must NOT be dropped from the
    // regenerated `.cl`. Before the fix, `generate_fns_and_macros` sourced a
    // UserFn's text from introspection only (its `.or(macro_table_sexp)`
    // covers macros, never UserFns), so a UserFn with an empty introspection
    // record was silently dropped. Rehydration re-reads the backing `.cl` and
    // populates the missing record. This test asserts that after rehydration,
    // the previously-empty UserFn regenerates back into the source.
    // spec: design/arch/fixmes/0220 §item-3; design/int/session-persistence.md §1.3
    #[test]
    fn rehydrate_recovers_cache_loaded_userfn_dropped_from_regen() {
        use cranelisp_types::{DefKind, Scheme, Type};
        use std::collections::HashMap;

        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        // Simulate a cache-restored module: a UserFn `Def` populates the
        // SymbolTable but the REPL-only Introspection map has NO record for it.
        let scheme = Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        };
        st.insert(
            "answer".into(),
            ModuleEntry::def(
                scheme,
                DefKind::UserFn {
                    fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0 },
                },
            )
            .build(),
        );

        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();

        // Without any introspection record, the UserFn is dropped from regen.
        let before = generate_module_source(&st, Some(&introspection), &module);
        assert!(
            !before.contains("answer"),
            "precondition: cache-loaded UserFn with no introspection is dropped: {before:?}"
        );

        // The backing `.cl` (the cache key) still holds the function source.
        let backing = "(defn answer [] 42)\n";
        let n = rehydrate_userfn_introspection_from_source(
            &st,
            &introspection,
            &module,
            backing,
        );
        assert_eq!(n, 1, "exactly one UserFn rehydrated");

        // After rehydration, the function regenerates back into the source.
        let after = generate_module_source(&st, Some(&introspection), &module);
        assert!(
            after.contains("answer"),
            "post-rehydration: UserFn is recovered into regenerated source: {after:?}"
        );
    }

    #[test]
    fn sexp_defines_symbol_matches_defining_forms() {
        let p = |s: &str| cranelisp_frontend::parse(s).unwrap().remove(0);
        assert!(sexp_defines_symbol(&p("(defn foo [] 1)"), "foo"));
        assert!(sexp_defines_symbol(&p("(deftype Point [:Int x])"), "Point"));
        assert!(sexp_defines_symbol(&p("(defmacro m [x] x)"), "m"));
        assert!(!sexp_defines_symbol(&p("(defn foo [] 1)"), "bar"));
        assert!(!sexp_defines_symbol(&p("(import [core [foo]])"), "foo"));
    }

    // FIXME 0343: a parent whose backing file holds an authored inline
    // `(mod child form…)` block (ModDecl retains `inline_body`) MUST NOT be
    // regenerated — regen from the parent table alone would emit a bare
    // `(mod child)` and DROP the child body from disk (data corruption). The
    // role gate `should_regenerate` returns `false` for such a parent.
    // spec: design/arch/fixmes/0343; repl/spec.md §15.4
    #[test]
    fn should_regenerate_false_when_submodule_retains_inline_body() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module);
        let p = |s: &str| cranelisp_frontend::parse(s).unwrap();
        st.submodules.push(ModDecl {
            name: "test".into(),
            visibility: cranelisp_types::Visibility::Public,
            inline_body: Some(p("(defn g [] 2)")),
            span: Span::SYNTHETIC,
        });
        assert!(
            !should_regenerate(&st),
            "a body-bearing (mod child …) parent MUST NOT regenerate (would drop the body)"
        );
    }

    // The gate fires ONLY for inline-body submodules — a manually-created /
    // already-extracted submodule (bare `(mod util)`, `inline_body: None`) does
    // NOT suppress regeneration; the child lives in its own file the regen never
    // touches.
    // spec: design/arch/fixmes/0343
    #[test]
    fn should_regenerate_true_for_bare_submodule_decl() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module);
        st.submodules.push(ModDecl {
            name: "util".into(),
            visibility: cranelisp_types::Visibility::Public,
            inline_body: None,
            span: Span::SYNTHETIC,
        });
        assert!(
            should_regenerate(&st),
            "a bare (mod util) submodule (no inline body) MUST regenerate normally"
        );
    }

    // A plain module with no submodules regenerates normally.
    #[test]
    fn should_regenerate_true_for_no_submodules() {
        let st = crate::code::SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        assert!(should_regenerate(&st));
    }

    #[test]
    fn atomic_write_creates_file() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("test.cl");
        atomic_write(&path, "(defn foo [] 42)\n").expect("write");
        let content = std::fs::read_to_string(&path).expect("read");
        assert_eq!(content, "(defn foo [] 42)\n");
    }

    // -----------------------------------------------------------------------
    // FIXME 0423 secondary symptom — annotation spacing on regen
    // -----------------------------------------------------------------------

    fn parse1(src: &str) -> Sexp {
        cranelisp_frontend::parse(src).unwrap().remove(0)
    }

    // The regen renderer MUST emit a COMPOUND type annotation with NO space
    // after `:` — `:(Option String)`, not `: (Option String)`. The reader
    // represents the compound annotation as a bare `Sexp::Symbol(":")` followed
    // by the type form; the generic `format_indented` joins siblings with a
    // space (the regression). `render_decl_sexp` suppresses that separator per
    // the `:Type`-binds-following-form reader-macro semantics.
    // spec: spec/08-modules.md §8.2.2 — regen annotation spacing (FIXME 0423)
    #[test]
    fn render_decl_compound_annotation_no_space_after_colon() {
        let sexp = parse1("(defn f [x] :(Option String) x)");
        let rendered = render_decl_sexp(&sexp);
        assert!(
            rendered.contains(":(Option String)"),
            "compound annotation must render with NO space after `:`: {rendered:?}"
        );
        assert!(
            !rendered.contains(": (Option String)"),
            "regen must NOT insert a space after `:` (FIXME 0423 regression): {rendered:?}"
        );
    }

    // A simple-symbol annotation (`:Int`) is a single `Sexp::Symbol(":Int")` and
    // already round-trips; verify the renderer leaves it intact.
    // spec: spec/08-modules.md §8.2.2
    #[test]
    fn render_decl_simple_annotation_unchanged() {
        let sexp = parse1("(defn g [] :Int 3)");
        let rendered = render_decl_sexp(&sexp);
        assert_eq!(rendered, "(defn g [] :Int 3)", "got {rendered:?}");
    }

    // The colon-binding suppression must also hold when the form breaks across
    // lines (long body forces the indented path) — the `:(…)` stays glued.
    // spec: spec/08-modules.md §8.2.2
    #[test]
    fn render_decl_compound_annotation_no_space_when_indented() {
        let sexp = parse1(
            "(defn h [:Int x] :(Option String) \
             (longerbody aaaaaaaa bbbbbbbb cccccccc dddddddd eeeeeeee))",
        );
        let rendered = render_decl_sexp(&sexp);
        assert!(
            rendered.contains(":(Option String)"),
            "indented compound annotation must glue `:` to its form: {rendered:?}"
        );
        assert!(
            !rendered.contains(": (Option String)"),
            "no space after `:` even when indented: {rendered:?}"
        );
    }

    // -----------------------------------------------------------------------
    // §8.16 module preamble — wiring + byte-stable regen round-trip
    // -----------------------------------------------------------------------

    // Wiring (§8.16.5 / design/frontend/module-preamble.md §5): loading a module
    // (here, applying preamble capture over its source) populates the live
    // `SymbolTable.module_preamble` from the leading comment block.
    // spec: spec/08-modules.md §8.16.2 — stored representation
    #[test]
    fn apply_module_preamble_populates_field_from_leading_comment_block() {
        let module = ModuleFullPath::from("user");
        let tables: DashMap<ModuleFullPath, crate::code::SessionSymbolTable> = DashMap::new();
        let source = ";; Module docs line 1\n;; line 2\n(defn f [] 0)\n";
        apply_module_preamble(&tables, &module, source);
        let st = tables.get(&module).expect("table created");
        assert_eq!(
            st.module_preamble.as_deref(),
            Some("Module docs line 1\nline 2"),
            "preamble text must be the marker-stripped, newline-joined block"
        );
    }

    // A module with NO leading comment block stores `None` (the common, valid
    // case — §8.16.2).
    // spec: spec/08-modules.md §8.16.2
    #[test]
    fn apply_module_preamble_none_when_no_leading_comment() {
        let module = ModuleFullPath::from("user");
        let tables: DashMap<ModuleFullPath, crate::code::SessionSymbolTable> = DashMap::new();
        apply_module_preamble(&tables, &module, "(defn f [] 0)\n");
        let st = tables.get(&module).expect("table created");
        assert_eq!(st.module_preamble, None);
    }

    // Inverse-pair invariant (§8.16.5 / §6.3): capture's strip (marker + one
    // space) ∘ re-emit's re-mark (`;; ` + line) == identity on the canonical
    // form. An unedited preamble re-emits byte-identically to its captured
    // source block, and re-capturing the regenerated head yields the same text.
    // spec: spec/08-modules.md §8.16.5 — byte-stable source-regen round-trip
    #[test]
    fn preamble_reemit_is_inverse_of_capture() {
        // Canonical `;;`-and-one-space block (the spec §8.16.1 idiom).
        let captured = cranelisp_frontend::capture_module_preamble(
            ";; Sudoku solver: constraint propagation +\n\
             ;; backtracking over a Vec-backed grid.\n\
             (mod solver)\n",
        )
        .expect("captured");
        assert_eq!(
            captured,
            "Sudoku solver: constraint propagation +\nbacktracking over a Vec-backed grid."
        );

        // Re-emit the stored text as the leading `;;` block.
        let block = generate_preamble(&captured);
        assert_eq!(
            block,
            ";; Sudoku solver: constraint propagation +\n\
             ;; backtracking over a Vec-backed grid."
        );

        // Re-capturing the re-emitted block (followed by a form) yields the
        // SAME stored text — the inverse-pair round-trip holds.
        let regen_source = format!("{block}\n(mod solver)\n");
        let recaptured = cranelisp_frontend::capture_module_preamble(&regen_source)
            .expect("recaptured");
        assert_eq!(recaptured, captured, "capture ∘ re-emit must be identity");

        // A bare-empty preamble line re-marks as bare `;;` and round-trips.
        let empty_line = generate_preamble("");
        assert_eq!(empty_line, ";;");
    }

    // End-to-end via `generate_module_source`: a module whose table carries a
    // preamble re-emits it as the leading `;;` section-0 block, ABOVE the first
    // form; a module with no preamble regenerates with no leading block.
    // spec: spec/08-modules.md §8.16.5 — canonical leading position
    #[test]
    fn generate_module_source_emits_preamble_section_zero() {
        use cranelisp_types::{DefKind, Scheme, Type, UserFnState};
        use std::collections::HashMap;

        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.module_preamble = Some("Header doc\nsecond line".to_string());
        let scheme = Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        };
        st.insert(
            "answer".into(),
            ModuleEntry::def(
                scheme,
                DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot: 0 },
                },
            )
            .build(),
        );
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "answer".into(),
        };
        introspection.entry(fq).or_default().sexp = Some(parse1("(defn answer [] 42)"));

        let out = generate_module_source(&st, Some(&introspection), &module);
        assert!(
            out.starts_with(";; Header doc\n;; second line\n"),
            "preamble must be the leading section-0 block: {out:?}"
        );
        // Re-capturing the regenerated source yields the same preamble text.
        assert_eq!(
            cranelisp_frontend::capture_module_preamble(&out).as_deref(),
            Some("Header doc\nsecond line"),
            "regenerated preamble must re-parse to the same text"
        );

        // No-preamble module: no leading `;;` block.
        st.module_preamble = None;
        let out_none = generate_module_source(&st, Some(&introspection), &module);
        assert!(
            !out_none.starts_with(";;"),
            "a no-preamble module must regenerate without a leading block: {out_none:?}"
        );
    }

}

