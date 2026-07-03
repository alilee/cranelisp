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
///
/// Docstring-aware (FIXME 0430, `design/int/session-persistence.md §11.3a`,
/// RATIFIED Option 1): `docstring` carries the LIVE `ModuleEntry::Def.docstring`,
/// which is AUTHORITATIVE. When `Some(text)`, the §5.12 docstring slot in the
/// `defn` form (a string literal between the function name and the param vector /
/// first variant) is emitted/replaced with `text`, and any docstring already
/// embedded in the stored sexp is DROPPED — the form never carries two docstrings.
/// When `None`, the stored sexp is rendered verbatim, so a never-`set-doc`'d def
/// keeps its own authored docstring (and a def with none stays byte-identical).
/// The stored sexp is NEVER mutated — the reconciler builds a fresh `Sexp` locally
/// (Principle 7: `set-doc` → `Def.docstring` is the one writer of the metadata).
fn render_decl_sexp(sexp: &Sexp, docstring: Option<&str>) -> String {
    match reconcile_docstring(sexp, docstring) {
        Some(reconciled) => render_decl_sexp_indented(&reconciled, 0),
        None => render_decl_sexp_indented(sexp, 0),
    }
}

/// Reconcile a live `Def.docstring` into a `(defn …)` / `(defn- …)` sexp per the
/// §11.3a authoritative-live rule. Returns:
///   - `Some(new_sexp)` — a freshly-built `defn` with `text` spliced into the
///     §5.12 docstring slot (replacing any existing leading docstring), when
///     `docstring == Some(text)` and `sexp` is a `defn`/`defn-` form.
///   - `None` — render the input unchanged: either `docstring == None` (the
///     stored sexp's own docstring, if any, round-trips), or `sexp` is not a
///     `defn` form (traits/types/macros pass `None` anyway).
///
/// The §5.12 slot rule MIRRORS the parser (`ast_builder::extract_optional_docstring`
/// at index 2): `children[2]` is the docstring iff it is a `Sexp::Str` (the param
/// vector / first variant always follows it, so there is no body-string ambiguity
/// at this position). The input sexp is cloned, never mutated.
fn reconcile_docstring(sexp: &Sexp, docstring: Option<&str>) -> Option<Sexp> {
    let text = docstring?;
    let (children, span) = match sexp {
        Sexp::List(c, s) => (c, *s),
        _ => return None,
    };
    let is_defn = matches!(
        children.first(),
        Some(Sexp::Symbol(head, _)) if head == "defn" || head == "defn-"
    );
    if !is_defn || children.len() < 2 {
        return None;
    }
    // Does the docstring slot (index 2) already hold a string literal?
    let existing_is_docstring = matches!(children.get(2), Some(Sexp::Str(..)));
    let mut new_children: Vec<Sexp> = Vec::with_capacity(children.len() + 1);
    new_children.push(children[0].clone()); // defn / defn-
    new_children.push(children[1].clone()); // name
    new_children.push(Sexp::Str(text.to_string(), span)); // live docstring (authoritative)
    // Skip the stored sexp's own docstring if present (never double-emit, §11.3a).
    let rest_start = if existing_is_docstring { 3 } else { 2 };
    new_children.extend(children[rest_start..].iter().cloned());
    Some(Sexp::List(new_children, span))
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

/// Set the module preamble field directly to the agent-supplied STRIPPED prose
/// (no `;;` markers) and persist it byte-stably (`design/int/agent.md §17.1`,
/// S89 Cluster C — the Document-mode write path, R4). Unlike
/// `apply_module_preamble` (which CAPTURES from `;;`-marked source on load), the
/// agent supplies the stripped prose — exactly the form `/doc <module>` reads
/// back — so the field is set directly. Only `module_preamble` is touched, so the
/// unmodified-rest-of-file invariant (§8.16.5 no-reflow) holds by construction;
/// `generate_preamble` re-emits the canonical `;; ` block on the next regen (the
/// byte-stable inverse of capture). Ensures the module table exists first.
#[cfg(feature = "agent")]
pub(crate) fn apply_preamble_edit(
    symbol_tables: &DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    module: &ModuleFullPath,
    new_preamble_text: &str,
) {
    cranelisp_types::ensure_module_exists(symbol_tables, module);
    if let Some(mut st) = symbol_tables.get_mut(module) {
        st.module_preamble = Some(new_preamble_text.to_string());
    }
}

/// Render stripped preamble prose as the canonical leading `;;` comment block —
/// the exact form `generate_module_source` emits at section 0, so the agent's
/// Document-mode consultative gate can SHOW the user precisely what it proposes
/// to record (`design/int/agent.md §17.2`). A `pub(crate)` window onto the
/// byte-stable `generate_preamble` emitter (Principle 7 — one emitter, not two).
#[cfg(feature = "agent")]
pub(crate) fn render_preamble_block(text: &str) -> String {
    generate_preamble(text)
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
            items.push((name.to_string(), render_decl_sexp(&sexp, None)));
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
            items.push((name.to_string(), render_decl_sexp(&sexp, None)));
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
    // Live docstrings, keyed by symbol name (FIXME 0430, §11.3a). The live
    // `ModuleEntry::Def.docstring` is AUTHORITATIVE — threaded into the renderer
    // at emit time so a `set-doc` edit round-trips through regen. Only `UserFn`
    // entries with a `Some` docstring are recorded; macros are out of scope for
    // S94 (a `defmacro` has no `set-doc` surface — they render with `None`).
    let mut docstrings: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();

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
            ModuleEntry::Def { kind, docstring, .. } => match kind.as_ref() {
                cranelisp_types::DefKind::Macro { macro_sexp, .. } => {
                    (true, Some(macro_sexp.clone()))
                }
                cranelisp_types::DefKind::UserFn { .. } => {
                    // Capture the live, authoritative docstring (§11.3a) so regen
                    // re-emits a `set-doc` edit into the §5.12 slot.
                    if let Some(doc) = docstring {
                        docstrings.insert(name.to_string(), doc.clone());
                    }
                    (false, None)
                }
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
    //
    // S102 CS-D1 — single-authority dedup (§15.4.7; s102-defect-wave.md §4.2):
    // N records sharing ONE authored form emit that form exactly once, at its
    // first position in the macros-first stream. Two shapes produce shared
    // authored forms: a macro-expansion-produced defmacro records the turn's
    // ORIGINAL outer form (as does the defn the same expansion produced —
    // e.g. `(mdef x 1)` under both `x` and `x-def`), and a literal
    // `(begin (defn a …) (defn b …))` records the begin under both names.
    // Emitting the authored form twice poisons the file: the original
    // re-expands at reload while its expansion artifacts are already
    // registered, and the two do not co-load (/port D1). Identity is the
    // authored form itself: (span, rendered text).
    let mut seen_authored: HashSet<(u32, u32, String)> = HashSet::new();
    let macros_sorted = dependency_sort(macro_items, st);
    let fns_sorted = dependency_sort(fn_items, st);
    macros_sorted
        .into_iter()
        .chain(fns_sorted)
        .filter(|(_, sexp)| {
            let span = sexp.span();
            seen_authored.insert((span.start, span.end, sexp.format_flat()))
        })
        // Macros carry `None` (they are absent from `docstrings`); UserFns thread
        // their live, authoritative docstring (§11.3a). The renderer is a strict
        // no-op when the lookup misses — a never-`set-doc`'d def stays unchanged.
        .map(|(name, sexp)| render_decl_sexp(&sexp, docstrings.get(&name).map(String::as_str)))
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
                    fn_state: cranelisp_types::UserFnState::Concrete { got_slot: 0, mode_summary: None },
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

    // Consumer-audit guard for the S101 `Def.callees` enrichment (FIXME 0470;
    // gate note 2). With the denser edge set — plain direct-call and
    // fn-as-value edges now recorded, where before only trait/sig-dispatch/
    // auto-curry edges existed — `dependency_sort` must still produce a
    // correct, complete emission order: callees before callers on acyclic
    // edges, termination + no item loss on the newly-representable cycles
    // (mutual recursion is a 2-cycle in the enriched graph), self-edges
    // filtered, cross-module edges ignored. The e2e cover is the existing
    // `repl_persist.rs` §15.4 round-trips; this pins the seam directly.
    // spec: tests/plan/s101-coverage-postmortem.md §2.1 item 4
    #[test]
    fn dependency_sort_correct_and_total_under_dense_callee_edges() {
        use cranelisp_types::{DefKind, Scheme, Type, UserFnState};
        use std::collections::HashMap as StdHashMap;

        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        let fq = |m: &str, s: &str| FQSymbol {
            module: ModuleFullPath::from(m),
            symbol: s.into(),
        };
        let mut insert_fn = |name: &str, slot: usize, callees: Vec<FQSymbol>| {
            let scheme = Scheme {
                type_vars: vec![],
                constraints: StdHashMap::new(),
                ty: Type::Int,
            };
            let mut entry = ModuleEntry::def(
                scheme,
                DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None },
                },
            )
            .build();
            if let ModuleEntry::Def { callees: c, .. } = &mut entry {
                *c = callees;
            }
            st.insert(name.into(), entry);
        };

        // Acyclic chain: top → mid → leaf (dense direct-call edges).
        insert_fn("leaf", 0, vec![]);
        insert_fn("mid", 1, vec![fq("user", "leaf")]);
        insert_fn("top", 2, vec![fq("user", "mid")]);
        // Mutual recursion: pa ↔ pb (a 2-cycle, newly representable with
        // enriched edges), plus a caller pc → pa whose in-degree never
        // resolves through the cycle.
        insert_fn("pa", 3, vec![fq("user", "pb")]);
        insert_fn("pb", 4, vec![fq("user", "pa")]);
        insert_fn("pc", 5, vec![fq("user", "pa")]);
        // Self-recursion (filtered by the `callee_name != name` guard) and a
        // cross-module edge (filtered by the `callee.module == st.path` guard).
        insert_fn("selfy", 6, vec![fq("user", "selfy"), fq("other", "leaf")]);

        let p = |s: &str| cranelisp_frontend::parse(s).unwrap().remove(0);
        let items: Vec<(String, Sexp)> = ["top", "mid", "leaf", "pa", "pb", "pc", "selfy"]
            .iter()
            .map(|n| (n.to_string(), p(&format!("(defn {n} [] 1)"))))
            .collect();

        let sorted = dependency_sort(items, &st);
        let order: Vec<&str> = sorted.iter().map(|(n, _)| n.as_str()).collect();

        // Termination + totality: every item exactly once, cycles included.
        assert_eq!(order.len(), 7, "no item lost or duplicated: {order:?}");
        let pos = |n: &str| {
            order
                .iter()
                .position(|x| *x == n)
                .unwrap_or_else(|| panic!("{n} missing from {order:?}"))
        };
        // Callee-before-caller on the acyclic chain.
        assert!(pos("leaf") < pos("mid"), "leaf before mid: {order:?}");
        assert!(pos("mid") < pos("top"), "mid before top: {order:?}");
    }

    // -----------------------------------------------------------------------
    // S102 CS-D1 — origin-uniform regen dedup (Matrix B: single-authority)
    // -----------------------------------------------------------------------

    fn userfn_entry(slot: usize) -> ModuleEntry<crate::code::Code> {
        use cranelisp_types::{DefKind, Scheme, Type, UserFnState};
        ModuleEntry::def(
            Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Int,
            },
            DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None },
            },
        )
        .build()
    }

    fn macro_entry(macro_sexp: Sexp) -> ModuleEntry<crate::code::Code> {
        use cranelisp_types::{DefKind, Scheme, Type};
        ModuleEntry::def(
            Scheme {
                type_vars: vec![],
                constraints: std::collections::HashMap::new(),
                ty: Type::Int,
            },
            DefKind::Macro { clauses_meta: vec![], macro_sexp },
        )
        .build()
    }

    // Matrix B {defmacro (macro-expansion artifact) × single-authority}: a
    // macro-defining-macro turn records the ORIGINAL outer form under BOTH the
    // produced macro (`x`) and the produced defn (`x-def`). Regen MUST emit
    // that authored form exactly once and MUST NOT emit the expansion
    // artifact — persisting both was /port D1's directory poison (the pair
    // does not co-load).
    // spec: repl/spec.md §15.1 — round-trip; §15.4 invariant 7
    #[test]
    fn regen_macro_expansion_artifact_emits_authored_origin_once() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let expanded_defmacro =
            parse1("(defmacro x [] (macros/SexpList (macros/SCons x-def macros/SNil)))");
        st.insert("x".into(), macro_entry(expanded_defmacro));
        st.insert("x-def".into(), userfn_entry(0));

        let original = parse1("(mdef x 1)");
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        for name in ["x", "x-def"] {
            let fq = FQSymbol { module: module.clone(), symbol: name.into() };
            introspection.entry(fq).or_default().sexp = Some(original.clone());
        }

        let out = generate_module_source(&st, Some(&introspection), &module);
        assert_eq!(
            out.matches("(mdef x 1)").count(),
            1,
            "the authored form is the single regeneration authority, emitted once: {out:?}"
        );
        assert!(
            !out.contains("defmacro"),
            "the expansion artifact must NOT co-persist with its origin (D1): {out:?}"
        );
    }

    // Matrix B {literal-begin multi-defn × single-authority}: a user-typed
    // `(begin (defn a …) (defn b …))` records the begin form under both names;
    // regen emits it once (the latent sibling of the D1 cell — same dedup).
    // spec: repl/spec.md §15.1
    #[test]
    fn regen_literal_begin_multi_defn_emits_once() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.insert("a".into(), userfn_entry(0));
        st.insert("b".into(), userfn_entry(1));

        let begin_form = parse1("(begin (defn a [] 1) (defn b [] 2))");
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        for name in ["a", "b"] {
            let fq = FQSymbol { module: module.clone(), symbol: name.into() };
            introspection.entry(fq).or_default().sexp = Some(begin_form.clone());
        }

        let out = generate_module_source(&st, Some(&introspection), &module);
        assert_eq!(
            out.matches("(begin").count(),
            1,
            "one authored begin form, one emission: {out:?}"
        );
    }

    // Control (negative boundary): two DISTINCT defns — same shape, different
    // names/spans — are NOT deduped; and a direct-authored defmacro still
    // emits its own defmacro form (the dedup keys on authored-form identity,
    // never on kind).
    // spec: repl/spec.md §15.1
    #[test]
    fn regen_dedup_neg_distinct_forms_and_direct_defmacro_all_emit() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.insert("f".into(), userfn_entry(0));
        st.insert("g".into(), userfn_entry(1));
        let twice = parse1("(defmacro twice [e] (add-i64 e e))");
        st.insert("twice".into(), macro_entry(twice.clone()));

        // Distinct spans: parse the two defns from one source string.
        let sexps = cranelisp_frontend::parse("(defn f [] 1)\n(defn g [] 1)").unwrap();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        introspection
            .entry(FQSymbol { module: module.clone(), symbol: "f".into() })
            .or_default()
            .sexp = Some(sexps[0].clone());
        introspection
            .entry(FQSymbol { module: module.clone(), symbol: "g".into() })
            .or_default()
            .sexp = Some(sexps[1].clone());
        introspection
            .entry(FQSymbol { module: module.clone(), symbol: "twice".into() })
            .or_default()
            .sexp = Some(twice);

        let out = generate_module_source(&st, Some(&introspection), &module);
        assert!(out.contains("(defn f [] 1)"), "f emitted: {out:?}");
        assert!(out.contains("(defn g [] 1)"), "g emitted: {out:?}");
        assert!(out.contains("(defmacro twice"), "direct defmacro emitted: {out:?}");
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
        let rendered = render_decl_sexp(&sexp, None);
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
        let rendered = render_decl_sexp(&sexp, None);
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
        let rendered = render_decl_sexp(&sexp, None);
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
    // FIXME 0430 — docstring-aware render_decl_sexp (§11.3a reconciliation)
    // -----------------------------------------------------------------------

    // Unit (regen reads live field, §11.4): a stored sexp with NO docstring +
    // a live `Def.docstring = Some("new doc")` emits a `defn` form carrying the
    // docstring in the §5.12 slot (a string literal between name and params).
    // spec: design/int/session-persistence.md §11.3a — live docstring authoritative
    #[test]
    fn render_decl_injects_live_docstring_when_sexp_has_none() {
        let sexp = parse1("(defn double [x] (add-i64 x x))");
        let rendered = render_decl_sexp(&sexp, Some("doubles its argument"));
        assert_eq!(
            rendered, "(defn double \"doubles its argument\" [x] (add-i64 x x))",
            "live docstring must be spliced into the §5.12 slot: {rendered:?}"
        );
    }

    // Unit (reconcile arm — the §11.3a load-bearing rule): a stored sexp that
    // ALREADY carries a docstring + a live `Def.docstring = Some("new")` emits the
    // NEW docstring ONLY — the old is dropped, exactly one docstring, never two.
    // spec: design/int/session-persistence.md §11.3a — no double-docstring hazard
    #[test]
    fn render_decl_live_docstring_replaces_sexp_docstring_no_duplicate() {
        let sexp = parse1("(defn f \"old doc\" [x] x)");
        let rendered = render_decl_sexp(&sexp, Some("new doc"));
        assert!(
            rendered.contains("\"new doc\""),
            "the live docstring must win: {rendered:?}"
        );
        assert!(
            !rendered.contains("old doc"),
            "the superseded stored-sexp docstring must be dropped: {rendered:?}"
        );
        assert_eq!(
            rendered.matches("new doc").count(),
            1,
            "the docstring must appear exactly once (no double-emit): {rendered:?}"
        );
    }

    // Unit (live None, sexp has docstring): a never-`set-doc`'d def with `None`
    // keeps its own authored docstring (the sexp round-trips unchanged).
    // spec: design/int/session-persistence.md §11.3a — None falls back to the sexp
    #[test]
    fn render_decl_none_keeps_sexp_docstring() {
        let sexp = parse1("(defn f \"authored doc\" [x] x)");
        let rendered = render_decl_sexp(&sexp, None);
        assert_eq!(
            rendered, "(defn f \"authored doc\" [x] x)",
            "with None the stored docstring round-trips: {rendered:?}"
        );
    }

    // Unit (no-docstring unchanged): `None` + a stored sexp with NO docstring
    // emits the `defn` exactly as before — a strict no-op (no spurious empty
    // string literal). Guards that Option 1 never injects when there is nothing.
    // spec: design/int/session-persistence.md §11.3a — strict no-op
    #[test]
    fn render_decl_none_no_docstring_unchanged() {
        let sexp = parse1("(defn f [x] x)");
        let rendered = render_decl_sexp(&sexp, None);
        assert_eq!(rendered, "(defn f [x] x)", "no-op when nothing to inject: {rendered:?}");
        assert!(!rendered.contains("\"\""), "no spurious empty docstring: {rendered:?}");
    }

    // Unit (round-trip): the emitted single-sig `defn` re-parses with the
    // docstring recovered in the right slot (no double docstring, no body-string
    // confusion). Mirrors the parser's `extract_optional_docstring` at index 2.
    // spec: design/int/session-persistence.md §11.3a — round-trip
    #[test]
    fn render_decl_injected_docstring_round_trips_single_sig() {
        let sexp = parse1("(defn double [x] (add-i64 x x))");
        let rendered = render_decl_sexp(&sexp, Some("the doc"));
        let reparsed = parse1(&rendered);
        let entry = cranelisp_frontend::build_form(&reparsed).expect("re-parses");
        let doc = match &entry[0] {
            cranelisp_types::ParsedEntry::Def { docstring, .. } => docstring.clone(),
            other => panic!("expected Def, got {other:?}"),
        };
        assert_eq!(doc.as_deref(), Some("the doc"), "docstring recovered in slot");
    }

    // Unit (round-trip, multi-sig): the docstring slot sits between the name and
    // the FIRST variant for a multi-clause defn, and re-parses correctly.
    // spec: design/int/session-persistence.md §11.3a — multi-sig slot
    #[test]
    fn render_decl_injected_docstring_round_trips_multi_sig() {
        let sexp = parse1("(defn f ([x] x) ([x y] x))");
        let rendered = render_decl_sexp(&sexp, Some("multi doc"));
        assert!(
            rendered.starts_with("(defn f \"multi doc\" ("),
            "docstring precedes the first variant: {rendered:?}"
        );
        let reparsed = parse1(&rendered);
        let entry = cranelisp_frontend::build_form(&reparsed).expect("re-parses");
        match &entry[0] {
            cranelisp_types::ParsedEntry::Def { docstring, variants, .. } => {
                assert_eq!(docstring.as_deref(), Some("multi doc"));
                assert_eq!(variants.len(), 2, "both variants preserved");
            }
            other => panic!("expected Def, got {other:?}"),
        }
    }

    // The reconciler only touches `defn`/`defn-` forms — a non-defn sexp (e.g. a
    // deftype) is never modified even if a docstring is passed (defensive; the
    // fns/macros loop only threads docstrings for UserFn defns).
    // spec: design/int/session-persistence.md §11.3a — defn-only slot rule
    #[test]
    fn render_decl_docstring_ignored_for_non_defn() {
        let sexp = parse1("(deftype Point [:Int x])");
        let rendered = render_decl_sexp(&sexp, Some("ignored"));
        assert!(!rendered.contains("ignored"), "non-defn must be untouched: {rendered:?}");
    }

    // End-to-end via `generate_module_source`: a UserFn whose live `Def.docstring`
    // is set but whose stored (introspection) sexp has NO docstring regenerates
    // WITH the docstring — the §17.15.3 durable promise at the regen seam.
    // spec: design/int/session-persistence.md §11.3a — set-doc persists via regen
    #[test]
    fn generate_module_source_emits_live_docstring() {
        use cranelisp_types::{DefKind, Scheme, Type, UserFnState};
        use std::collections::HashMap;

        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let scheme = Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        };
        st.insert(
            "double".into(),
            ModuleEntry::def(
                scheme,
                DefKind::UserFn {
                    fn_state: UserFnState::Concrete { got_slot: 0, mode_summary: None },
                },
            )
            .docstring("doubles its argument")
            .build(),
        );
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "double".into(),
        };
        introspection.entry(fq).or_default().sexp =
            Some(parse1("(defn double [x] (add-i64 x x))"));

        let out = generate_module_source(&st, Some(&introspection), &module);
        assert!(
            out.contains("(defn double \"doubles its argument\" [x] (add-i64 x x))"),
            "regen must emit the live docstring in the §5.12 slot: {out:?}"
        );
        assert_eq!(
            out.matches("doubles its argument").count(),
            1,
            "exactly one docstring in the regenerated source: {out:?}"
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
                    fn_state: UserFnState::Concrete { got_slot: 0, mode_summary: None },
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

