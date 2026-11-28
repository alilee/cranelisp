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

use std::io::Write;
use std::path::Path;

use cranelisp_types::{
    Binding, CallableOrigin, Decl, ExportSpec, FQSymbol, ImportEntry, ImportNames, ImportSpec,
    ModDecl, ModuleFullPath, ModuleName, PlatformSpec, Sexp, TypeRecord,
};

use dashmap::DashMap;

use crate::session_v4::{AuthoredPosition, EntryKey, Introspection};

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
/// (`src/AGENTS.md` testability discipline; mirrors `splice_inline_mod_to_bare`
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
/// Pure function: reads data, returns source text, or refuses with every
/// selected entry that has no recorded authored form (§2.4.3) rather than
/// omit it. After the preamble, the structural sections follow repl §15.4
/// rule 4 (platforms, submodules, exports, imports), and the definitions
/// follow in one sequence in authorship order (rule 2;
/// `design/int/s125-binary-clean.md` §4.2).
///
/// Sprint 58 Step 5a: structural decls read directly from
/// `symbol_table.{submodules, platforms, imports, exports}`. The implicit
/// prelude `(import [prelude [*]])` is suppressed by `generate_imports`
/// itself — `imports` records only user-authored forms (CP3 / option (b),
/// see `design/int/int.md` §6.5) but the filter remains as a
/// belt-and-braces guard.
pub(crate) fn generate_module_source(
    symbol_table: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> Result<String, UnrenderedEntries> {
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

    // Structural sections, in repl §15.4 rule 4's order: platforms,
    // submodules, exports, imports.
    let structural = [
        generate_platforms(&symbol_table.platforms),
        generate_mod_decls(&symbol_table.submodules),
        generate_exports(&symbol_table.exports),
        generate_imports(&symbol_table.imports),
    ];
    sections.extend(structural.into_iter().filter(|section| !section.is_empty()));

    // Definitions, one sequence in authorship order (rule 2).
    let definitions = generate_definitions(symbol_table, introspection, module_path)?;
    if !definitions.is_empty() {
        sections.push(definitions);
    }

    let mut result = sections.join("\n\n");
    if !result.is_empty() {
        result.push('\n');
    }
    Ok(result)
}

/// Entries a regeneration selected but could not render because no authored
/// form was recorded for them (`design/int/session-persistence.md` §2.4.3).
/// Writing the module without them would lose their source at the next start.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnrenderedEntries(Vec<Unrendered>);

/// One entry a regeneration could not render.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Unrendered {
    /// A named definition of the module.
    Named(cranelisp_types::Symbol),
    /// An implementation written in the module, named by its settled pair.
    Impl {
        trait_name: cranelisp_types::FQTraitName,
        impl_type: cranelisp_types::FQTypeName,
    },
}

impl std::fmt::Display for Unrendered {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unrendered::Named(name) => write!(f, "`{name}`"),
            Unrendered::Impl {
                trait_name,
                impl_type,
            } => write!(f, "`impl {trait_name} for {impl_type}`"),
        }
    }
}

impl std::fmt::Display for UnrenderedEntries {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names: Vec<String> = self.0.iter().map(Unrendered::to_string).collect();
        f.write_str(&names.join(", "))
    }
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

/// One `(platform …)` form per platform, in the table's order, which is the
/// order they were entered (repl §15.4 rule 4).
fn generate_platforms(specs: &[PlatformSpec]) -> String {
    first_occurrences(specs.iter().map(|spec| format!("(platform {})", spec.name))).join("\n")
}

/// One `(import [...])` form per module spec, in the table's order (repl
/// §15.4 rule 4; `design/int/s125-binary-clean.md` §4.6, R4): a multi-module
/// `import` contributes one entry per spec, and an exact repeat of an earlier
/// spec is written once. The implicit prelude import is filtered.
fn generate_imports(specs: &[ImportSpec]) -> String {
    let user_authored = specs.iter().filter(|s| {
        !(s.module_path == "prelude" && s.names == ImportNames::Glob && s.alias.is_none())
    });
    first_occurrences(user_authored.map(|spec| {
        format!(
            "(import [{}])",
            render_pair(&spec.module_path, spec.alias.as_ref(), &spec.names)
        )
    }))
    .join("\n")
}

/// `forms` in order, each exact repeat of an earlier one dropped.
fn first_occurrences(forms: impl Iterator<Item = String>) -> Vec<String> {
    let mut seen = std::collections::HashSet::new();
    forms.filter(|form| seen.insert(form.clone())).collect()
}

fn generate_exports(specs: &[ExportSpec]) -> String {
    if specs.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = specs
        .iter()
        .map(|spec| render_pair(&spec.module_path, spec.alias.as_ref(), &spec.names))
        .collect();
    format!("(export [{}])", parts.join(" "))
}

/// One `module-spec names-list` pair: `m` or `(m alias)`, then the list.
fn render_pair(
    module_path: &ModuleFullPath,
    alias: Option<&ModuleName>,
    names: &ImportNames,
) -> String {
    let module_spec = match alias {
        Some(alias) => format!("({module_path} {alias})"),
        None => module_path.to_string(),
    };
    let names_list = match names {
        ImportNames::Glob => "[*]".to_string(),
        // `[*]` is the glob only as the sole element (spec §8.3.2), so a lone
        // `*` entry keeps its rename form; beside others it is the operator.
        ImportNames::Specific(entries) if is_lone_star(entries) => "[(* *)]".to_string(),
        ImportNames::Specific(entries) => {
            let rendered: Vec<String> = entries.iter().map(render_entry).collect();
            format!("[{}]", rendered.join(" "))
        }
        ImportNames::None => "[]".to_string(),
    };
    format!("{module_spec} {names_list}")
}

fn is_lone_star(entries: &[ImportEntry]) -> bool {
    matches!(entries, [only] if render_entry(only) == "*")
}

/// A names-list entry as written: a `Name` whose `local` is the member its
/// `source` would bind renders as `source` (`Shade.Blue`, `Some`), any other
/// as the rename `(source local)`, and a member glob as `Parent.*`.
fn render_entry(entry: &ImportEntry) -> String {
    match entry {
        ImportEntry::Name { source, local }
            if local.as_ref() == cranelisp_types::bare_member_name(source.as_ref()) =>
        {
            source.to_string()
        }
        ImportEntry::Name { source, local } => format!("({source} {local})"),
        ImportEntry::MemberGlob(parent) => format!("{parent}.*"),
        other => unreachable!(
            "invariant: the frontend produces only `Name` and `MemberGlob` entries, got {other:?}"
        ),
    }
}

/// Does `source` re-parse to exactly the recorded `sexp`? (S102 CS-D2 — the
/// consistency gate for verbatim source-first emission.)
///
/// The comparison is reader-desugar-aware: the parse of a reader-shorthand
/// text (`` `(add-i64 ~e ~e) ``) yields the SAME desugared structure
/// (`(quasiquote (add-i64 (unquote e) (unquote e)))`) as the recorded sexp,
/// so authored shorthand passes while a stale / mis-sliced / garbage `source`
/// (whose parse fails, yields a different form count, or a different
/// structure) fails and the caller falls back to the reconciled sexp render —
/// verbatim emission can never corrupt the regenerated file.
pub(crate) fn sexp_matches_source(sexp: &Sexp, source: &str) -> bool {
    match cranelisp_frontend::parse(source) {
        Ok(forms) if forms.len() == 1 => forms[0].format_flat() == sexp.format_flat(),
        _ => false,
    }
}

/// The consistency-gated verbatim slice of `form` out of `text` (S102 CS-D2,
/// §15.4 rule 1, §15.1 authorship fidelity): the form's span slice must
/// re-parse to exactly the recorded form (`sexp_matches_source` is
/// reader-desugar-aware, so authored shorthand like `` `(… ~e) `` passes).
/// Returns `None` — callers fall back to `pretty_print` — when the span is out
/// of bounds / off a char boundary, or the slice does not match (e.g. a REPL
/// turn's fresh 0-based spans against a module's load-time file text). Shared
/// by `process_form::verbatim_source_slice` (live-turn capture) and the
/// introspection rehydrator below (S102 W5R M-5 — single gate, Principle 7).
pub(crate) fn verbatim_slice(form: &Sexp, text: &str) -> Option<String> {
    let span = form.span();
    let slice = text.get(span.start as usize..span.end as usize)?;
    if sexp_matches_source(form, slice) {
        Some(slice.to_string())
    } else {
        None
    }
}

/// Extract the §5.12 docstring-slot string from a parsed `defn`/`defn-` form
/// (`children[2]` is the docstring iff it is a string literal — mirrors
/// `ast_builder::extract_optional_docstring`).
fn form_docstring(form: &Sexp) -> Option<String> {
    let Sexp::List(children, _) = form else {
        return None;
    };
    let is_defn = matches!(
        children.first(),
        Some(Sexp::Symbol(head, _)) if head == "defn" || head == "defn-"
    );
    if !is_defn {
        return None;
    }
    match children.get(2) {
        Some(Sexp::Str(text, _)) => Some(text.clone()),
        _ => None,
    }
}

/// Choose the emitted text for one fn/macro item (S102 CS-D2 — source-text-
/// first emission, `design/int/s102-defect-wave.md` §4.2 rule 2): the verbatim
/// recorded `source` when present and CONSISTENT — it re-parses to the
/// recorded sexp AND already carries the live docstring in the §5.12 slot
/// (the reconciling renderer exists precisely because `Def.docstring` can be
/// edited out-of-band — `set-doc`, agent Document-mode; those fall back to
/// the render, which splices the live docstring); otherwise the reconciled
/// sexp render (byte-behaviour identical to pre-D2 for entries with no
/// verbatim record).
fn emit_decl_text(sexp: &Sexp, source: Option<&str>, live_doc: Option<&str>) -> String {
    if let Some(src) = source {
        let src = src.trim();
        if sexp_matches_source(sexp, src) {
            let doc_consistent = match live_doc {
                None => true,
                Some(d) => cranelisp_frontend::parse(src)
                    .ok()
                    .and_then(|mut v| {
                        if v.len() == 1 {
                            Some(v.remove(0))
                        } else {
                            None
                        }
                    })
                    .and_then(|form| form_docstring(&form))
                    .is_some_and(|doc| doc == d),
            };
            if doc_consistent {
                return src.to_string();
            }
        }
    }
    render_decl_sexp(sexp, live_doc)
}

/// Choose the emitted text for one definition from its record: source-text
/// first through the shared `emit_decl_text` gate when the record carries a
/// form, splicing `live_doc` into a function's §5.12 slot.
///
/// The `(None, Some(source))` arm is a record that holds authored text only,
/// as a REPL declaration's may (`eval::record_defining_turn_source`): the
/// verbatim text is emitted, gated on it re-parsing to a single well-formed
/// form, and that parse is its authored form. `None` ⇒ nothing renderable is
/// recorded ⇒ the caller reports the entry as unrendered (§2.4.3).
fn emit_decl_or_source(
    sexp: Option<Sexp>,
    source: Option<String>,
    live_doc: Option<&str>,
) -> Option<RenderedDecl> {
    match (sexp, source) {
        (Some(sexp), src) => Some(RenderedDecl {
            text: emit_decl_text(&sexp, src.as_deref(), live_doc),
            form: sexp.format_flat(),
        }),
        (None, Some(src)) => {
            let trimmed = src.trim();
            match cranelisp_frontend::parse(trimmed) {
                Ok(forms) if forms.len() == 1 => Some(RenderedDecl {
                    form: forms[0].format_flat(),
                    text: trimmed.to_string(),
                }),
                _ => None,
            }
        }
        (None, None) => None,
    }
}

/// One declaration's authored form, flat, and the text emitted for it.
struct RenderedDecl {
    form: String,
    text: String,
}

// ---------------------------------------------------------------------------
// The section selector (design/int/s125-binary-clean.md §4.1)
// ---------------------------------------------------------------------------

/// What regeneration does with one binding of the module's table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Persistence {
    /// The binding is module content, written from its record.
    Persisted(PersistedKind),
    /// The binding is not module content, for the reason given.
    Excluded(Exclusion),
}

/// The kinds of binding a module file holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PersistedKind {
    /// A single-signature function.
    Function,
    /// A multi-signature family, under its base name (ACT-1068).
    Family,
    Macro,
    /// A defined type: a sum or enum type, or a product type through its
    /// constructor's type facet.
    Type,
    Trait,
}

/// Why a binding is not written. An implementation is written from the
/// module's written-implementation records, never from a binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Exclusion {
    /// A synthetic internal name: an `__expr` wrapper, a mangled variant.
    Internal,
    /// A minted instance of a template, product constructors included
    /// (ACT-1101): the definitions that use it demand it again.
    MintedInstance,
    /// A sum type's constructor, written with its type.
    Constructor,
    /// A product field accessor, written with its type.
    Accessor,
    /// A method body of a trait implementation, written with its `impl`.
    ImplementationMethod,
    /// A trait's method declaration, written with its trait.
    TraitMethod,
    /// A trait implementation's discovery shell.
    ImplShell,
    SpecialForm,
    IntrinsicType,
    Primitive,
    PlatformEffect,
}

/// Classify one binding. Every `Decl` variant and callable origin is matched
/// with no wildcard, so a new variant does not compile until it is
/// classified. Instances are excluded before any facet is read.
fn persistence(name: &str, entry: &Binding<crate::code::Code>) -> Persistence {
    use Persistence::{Excluded, Persisted};
    if crate::worker::is_internal_listing_name(name) {
        return Excluded(Exclusion::Internal);
    }
    if crate::worker::is_internal_listing_entry(name, entry) {
        return Excluded(Exclusion::MintedInstance);
    }
    match &entry.declaration {
        Decl::Callable(callable) => match &callable.origin {
            CallableOrigin::Plain => Persisted(PersistedKind::Function),
            CallableOrigin::Ctor {
                type_def: Some(_), ..
            } => Persisted(PersistedKind::Type),
            CallableOrigin::Ctor { type_def: None, .. } => Excluded(Exclusion::Constructor),
            CallableOrigin::Accessor { .. } => Excluded(Exclusion::Accessor),
            CallableOrigin::TraitMethod { .. } => Excluded(Exclusion::ImplementationMethod),
            CallableOrigin::RustPrimitive => Excluded(Exclusion::Primitive),
            CallableOrigin::PlatformEffect { .. } => Excluded(Exclusion::PlatformEffect),
        },
        Decl::Overloaded(_) => Persisted(PersistedKind::Family),
        Decl::Macro(_) => Persisted(PersistedKind::Macro),
        Decl::TraitMethod(_) => Excluded(Exclusion::TraitMethod),
        Decl::Type(TypeRecord::Defined { .. }) => Persisted(PersistedKind::Type),
        Decl::Type(TypeRecord::Intrinsic { .. }) => Excluded(Exclusion::IntrinsicType),
        Decl::Trait(_) => Persisted(PersistedKind::Trait),
        Decl::ImplShell(_) => Excluded(Exclusion::ImplShell),
        Decl::SpecialForm(_) => Excluded(Exclusion::SpecialForm),
    }
}

// ---------------------------------------------------------------------------
// Definitions in authorship order (design/int/s125-binary-clean.md §4.2)
// ---------------------------------------------------------------------------

/// One persisted definition: its record's key, its authorship position and
/// its rendering.
struct Definition {
    key: cranelisp_types::Symbol,
    position: Option<AuthoredPosition>,
    decl: RenderedDecl,
}

/// The module's definitions, one sequence in authorship order (repl §15.4
/// rule 2), or every selected entry that has no recorded authored form.
fn generate_definitions(
    st: &crate::code::SessionSymbolTable,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
) -> Result<String, UnrenderedEntries> {
    let mut unrendered = Vec::new();
    let mut definitions = Vec::new();
    for (name, entry) in st.all_symbols() {
        let kind = match persistence(name.as_ref(), entry) {
            Persistence::Persisted(kind) => kind,
            Persistence::Excluded(reason) => {
                if std::env::var("CRANELISP_MODULE_TRACE").is_ok() {
                    eprintln!("module-trace: regeneration excludes {name}: {reason:?}");
                }
                continue;
            }
        };
        let record = authored_record(introspection, module_path, name);
        let (fallback, live_doc) = match (&entry.declaration, kind) {
            (Decl::Macro(declaration), _) => (Some(declaration.macro_sexp.clone()), None),
            (Decl::Callable(callable), PersistedKind::Function) => {
                (None, callable.docstring.as_deref())
            }
            (Decl::Overloaded(family), _) => (None, family.docstring.as_deref()),
            _ => (None, None),
        };
        match emit_decl_or_source(record.sexp.or(fallback), record.source, live_doc) {
            Some(decl) => definitions.push(Definition {
                key: name.clone(),
                position: record.position,
                decl,
            }),
            None => unrendered.push(Unrendered::Named(name.clone())),
        }
    }
    // "The impls written in module M" are M's `written_trait_impls` records
    // (`design/int/session-persistence.md` §12.3), each identified by the
    // injective key its live turn and rehydration record its form under
    // (`design/int/int.md` §6.13). An impl of M's trait written in another
    // module is that module's record: a legal exclusion.
    for record in st
        .written_trait_impls
        .iter()
        .filter(|record| record.impl_module == *module_path)
    {
        let key = crate::session_v4::impl_identity(record).symbol;
        let authored = authored_record(introspection, module_path, &key);
        match emit_decl_or_source(authored.sexp, authored.source, None) {
            Some(decl) => definitions.push(Definition {
                key,
                position: authored.position,
                decl,
            }),
            None => unrendered.push(Unrendered::Impl {
                trait_name: record.trait_name.clone(),
                impl_type: record.impl_type.clone(),
            }),
        }
    }
    if !unrendered.is_empty() {
        return Err(UnrenderedEntries(unrendered));
    }
    definitions.sort_by(|a, b| {
        (
            a.position.is_none(),
            a.position,
            &a.decl.form,
            a.key.as_ref(),
        )
            .cmp(&(
                b.position.is_none(),
                b.position,
                &b.decl.form,
                b.key.as_ref(),
            ))
    });
    Ok(emit_definitions(&definitions))
}

/// The authored carriers a definition is written from.
struct AuthoredRecord {
    sexp: Option<Sexp>,
    source: Option<String>,
    position: Option<AuthoredPosition>,
}

/// The record of `name`'s authored form, empty when none is recorded. The
/// verbatim `source` text is the S102 CS-D2 emission authority (§15.4 rule 1,
/// §15.1 authorship fidelity); the `sexp` remains the structural authority
/// (dedup identity, render fallback).
fn authored_record(
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module_path: &ModuleFullPath,
    name: &cranelisp_types::Symbol,
) -> AuthoredRecord {
    let fq = FQSymbol {
        module: module_path.clone(),
        symbol: name.clone(),
    };
    match introspection.and_then(|m| m.get(&fq)) {
        Some(record) => AuthoredRecord {
            sexp: record.sexp.clone(),
            source: record.source.clone(),
            position: record.position,
        },
        None => AuthoredRecord {
            sexp: None,
            source: None,
            position: None,
        },
    }
}

/// Write each entry once, in the definitions' authored order
/// (`design/int/s125-binary-clean.md` §4.2). The definitions a macro call
/// generated share its entry, its position and its authored form, so the call
/// is written once: a second copy poisons the file, since the call re-expands
/// at reload while its artifacts are already registered. A form at a position
/// is never dropped for a different form's sake.
fn emit_definitions(definitions: &[Definition]) -> String {
    let mut written: Vec<String> = Vec::new();
    let mut entry_at: Option<(AuthoredPosition, String)> = None;
    for definition in definitions {
        if let Some(position) = definition.position {
            let form = &definition.decl.form;
            if entry_at
                .as_ref()
                .is_some_and(|(at, seen)| *at == position && seen == form)
            {
                continue;
            }
            entry_at = Some((position, form.clone()));
        }
        written.push(definition.decl.text.clone());
    }
    written.join("\n\n")
}

// ---------------------------------------------------------------------------
// Backing-file rehydration (design/int/session-persistence.md §2.4.2)
// ---------------------------------------------------------------------------

/// Fill every missing authored-form record of `module_path` from its backing
/// file (`design/int/session-persistence.md` §2.4.2).
///
/// Cache restore and a fresh file load of declarations install entries
/// without records; the backing file they were installed from supplies them.
/// Each top-level native definition form is keyed as a live turn keys it and
/// fills that key's record only when the key is live and the record has
/// neither form nor text. A legacy file's `begin` dissolves as a load
/// dissolves it: each member records its own form at its own file position
/// (`design/int/s125-binary-clean.md` §4.2). A text-only record is a REPL
/// declaration that the file may hold an older generation of, so it is never
/// replaced. Returns the number of records filled; an unparseable file fills
/// none.
pub(crate) fn rehydrate_introspection_from_source(
    st: &crate::code::SessionSymbolTable,
    introspection: &DashMap<FQSymbol, Introspection>,
    module_path: &ModuleFullPath,
    backing_source: &str,
) -> usize {
    use crate::session_v4::{ImplRecordMatch, impl_identity, match_impl_record};
    let Ok(forms) = cranelisp_frontend::parse(backing_source) else {
        return 0;
    };

    let mut filled = 0;
    for form in &forms {
        for (member, key) in entry_keys(form, module_path) {
            // An impl form that no single record carries stays unkeyed; the
            // regeneration then reports its record as unrendered (§2.4.3).
            let symbol = match key {
                EntryKey::Name(symbol) if st.get(symbol.as_ref()).is_some() => symbol,
                EntryKey::Impl(label) => {
                    match match_impl_record(&st.written_trait_impls, module_path, &label) {
                        ImplRecordMatch::One(record) => impl_identity(record).symbol,
                        ImplRecordMatch::Unmatched | ImplRecordMatch::Several => continue,
                    }
                }
                EntryKey::Name(_) => continue,
            };
            let mut record = introspection
                .entry(FQSymbol {
                    module: module_path.clone(),
                    symbol,
                })
                .or_default();
            if record.sexp.is_some() || record.source.is_some() {
                continue;
            }
            record.source = Some(
                verbatim_slice(&member, backing_source)
                    .unwrap_or_else(|| crate::pretty::pretty_print_plain(&member)),
            );
            record.position = record
                .position
                .or(Some(AuthoredPosition::in_file(member.span().start)));
            record.sexp = Some(member);
            filled += 1;
        }
    }
    filled
}

/// The keys one top-level form's definitions record under before `impl`
/// identities settle, each with the member form that defines it: its own, or
/// each member's of a `begin`, recursively. Structural forms, expressions and
/// macro calls define none, and a member that does not build is skipped.
pub(crate) fn entry_keys(form: &Sexp, module_path: &ModuleFullPath) -> Vec<(Sexp, EntryKey)> {
    use crate::process_form::form_dispatch::{FormKind, classify_form};
    cranelisp_frontend::flatten_begin(form.clone())
        .into_iter()
        .filter_map(|member| {
            let key = if cranelisp_frontend::is_defmacro(&member) {
                EntryKey::Name(cranelisp_frontend::parse_defmacro(&member).ok()?.name)
            } else {
                if !matches!(classify_form(&member, module_path), Ok(FormKind::Regular)) {
                    return None;
                }
                let built =
                    crate::worker::build_program_compat(std::slice::from_ref(&member)).ok()?;
                let [top] = built.as_slice() else {
                    return None;
                };
                match top {
                    cranelisp_types::TopLevel::TraitImpl(trait_impl) => {
                        EntryKey::Impl(trait_impl.authored_label())
                    }
                    _ => match crate::session_v4::definition_identity(module_path, top)? {
                        crate::session_v4::BuiltIdentity::Keyed(symbol) => {
                            EntryKey::Name(symbol.symbol)
                        }
                        crate::session_v4::BuiltIdentity::Impl(_) => return None,
                    },
                }
            };
            Some((member, key))
        })
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
    use cranelisp_types::{
        Binding, CallableOrigin, Decl, DefnVariant, Expr, MonoDefnVariant, Realization, Scheme,
        Span, Symbol, TraitRecord, Type, TypeRecord, Visibility,
    };

    fn int_scheme() -> Scheme {
        Scheme {
            type_vars: Vec::new(),
            constraints: std::collections::HashMap::new(),
            ty: Type::Int,
        }
    }

    fn install_userfn(
        table: &mut crate::code::SessionSymbolTable,
        name: &str,
        expected_slot: usize,
        callees: Vec<FQSymbol>,
    ) {
        install_callable(table, name, expected_slot, callees, CallableOrigin::Plain);
    }

    fn install_callable(
        table: &mut crate::code::SessionSymbolTable,
        name: &str,
        expected_slot: usize,
        callees: Vec<FQSymbol>,
        origin: CallableOrigin,
    ) {
        let variant = DefnVariant {
            params: Vec::new(),
            body: Expr::IntLit {
                value: 0,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::SYNTHETIC,
        };
        let view = MonoDefnVariant {
            name: Symbol::from(name),
            params: Vec::new(),
            body: cranelisp_types::test_support::lenient_from_expr(
                &variant.body,
                &Default::default(),
                &Default::default(),
                &Default::default(),
            ),
            span: Span::SYNTHETIC,
            mode_summary: None,
        };
        let slot = table
            .install_concrete(
                Symbol::from(name),
                int_scheme(),
                Vec::new(),
                None,
                expected_slot as u64,
                origin,
                Realization::Body { view, code: None },
                Some(variant),
                callees,
                Visibility::Public,
            )
            .expect("user-function fixture installs through lifecycle funnel");
        assert_eq!(slot.index(), expected_slot);
    }

    fn regen_ok(
        st: &crate::code::SessionSymbolTable,
        introspection: Option<&DashMap<FQSymbol, Introspection>>,
        module: &ModuleFullPath,
    ) -> String {
        generate_module_source(st, introspection, module)
            .unwrap_or_else(|unrendered| panic!("unexpected refusal for {unrendered}"))
    }

    fn install_macro(table: &mut crate::code::SessionSymbolTable, name: &str, macro_sexp: Sexp) {
        crate::repl::test_support::install_macro_fixture(
            table,
            name,
            macro_sexp,
            Vec::new(),
            Visibility::Public,
        );
    }

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
            names: ImportNames::Specific(vec![
                crate::imports::plain_entry("foo"),
                crate::imports::plain_entry("bar"),
            ]),
            span: Span::SYNTHETIC,
        }];
        assert_eq!(generate_imports(&specs), "(import [core [foo bar]])");
    }

    fn import_spec(module: &str, names: ImportNames) -> ImportSpec {
        ImportSpec {
            module_path: module.into(),
            alias: None,
            names,
            span: Span::SYNTHETIC,
        }
    }

    fn export_spec(module: &str, names: ImportNames) -> ExportSpec {
        ExportSpec {
            module_path: module.into(),
            alias: None,
            names,
            span: Span::SYNTHETIC,
        }
    }

    fn names(entries: &[ImportEntry]) -> ImportNames {
        ImportNames::Specific(entries.to_vec())
    }

    fn rename(source: &str, local: &str) -> ImportEntry {
        ImportEntry::Name {
            source: Symbol::from(source),
            local: Symbol::from(local),
        }
    }

    // spec: repl/spec/15-session-persistence.md §15.4 rule 4;
    // design/int/s125-binary-clean.md §4.6 R4 — one `import` form per spec, in
    // the table's order: specs of one module are not merged, and a glob, a
    // rename and a name-less spec each keep their own form.
    #[test]
    fn imports_write_one_form_per_spec_in_table_order() {
        let plain = |name: &str| names(&[crate::imports::plain_entry(name)]);
        let specs = vec![
            import_spec("aa", plain("a")),
            import_spec("bb", plain("b")),
            import_spec("aa", plain("c")),
            import_spec("m", ImportNames::Glob),
            import_spec("m", names(&[rename("f", "g")])),
            import_spec("m", ImportNames::None),
        ];
        assert_eq!(
            generate_imports(&specs),
            "(import [aa [a]])\n(import [bb [b]])\n(import [aa [c]])\n\
             (import [m [*]])\n(import [m [(f g)]])\n(import [m []])"
        );
    }

    // spec: repl/spec/15-session-persistence.md §15.4 rule 4;
    // design/int/s125-binary-clean.md §4.6 R4 — an exact repeat of an earlier
    // spec is written once, at its first place.
    #[test]
    fn a_repeated_import_spec_is_written_once() {
        let list = import_spec("m", names(&[crate::imports::plain_entry("f")]));
        let other = import_spec("n", ImportNames::Glob);
        assert_eq!(
            generate_imports(&[list.clone(), other.clone(), list, other]),
            "(import [m [f]])\n(import [n [*]])"
        );
    }

    // spec: repl/spec/15-session-persistence.md §15.4 rule 4;
    // design/int/s125-binary-clean.md §4.6 R4 — platforms keep their entered
    // order, a repeat written once.
    #[test]
    fn platforms_keep_their_entered_order() {
        let platform = |name: &str| PlatformSpec {
            name: name.to_string(),
            span: Span::SYNTHETIC,
        };
        assert_eq!(
            generate_platforms(&[
                platform("test-capture"),
                platform("stdio"),
                platform("test-capture"),
            ]),
            "(platform test-capture)\n(platform stdio)"
        );
    }

    // spec: spec/08-modules.md §8.3.2; repl/spec/15-session-persistence.md §15.4
    // rule 1; design/int/int.md §6.13 (a lone `*` entry) — a list whose sole
    // entry is `*` renders it in rename form, for an import and an export, so
    // it does not read back as the glob; beside another entry `*` stays bare.
    #[test]
    fn a_lone_star_entry_renders_in_rename_form() {
        let star = crate::imports::plain_entry("*");
        let lone = names(std::slice::from_ref(&star));
        let multi = names(&[crate::imports::plain_entry("+"), star.clone()]);
        assert_eq!(
            generate_imports(&[import_spec("m", lone.clone())]),
            "(import [m [(* *)]])"
        );
        assert_eq!(
            generate_exports(&[export_spec("m", lone)]),
            "(export [m [(* *)]])"
        );
        assert_eq!(
            generate_imports(&[import_spec("m", multi.clone())]),
            "(import [m [+ *]])"
        );
        assert_eq!(
            generate_exports(&[export_spec("m", multi)]),
            "(export [m [+ *]])"
        );
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
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());

        // Simulate a cache-restored module: a UserFn `Def` populates the
        // SymbolTable but the REPL-only Introspection map has NO record for it.
        install_userfn(&mut st, "answer", 0, Vec::new());

        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();

        // Without any introspection record, regeneration refuses (§2.4.3).
        let before = generate_module_source(&st, Some(&introspection), &module);
        assert_eq!(
            before.map_err(|unrendered| unrendered.0),
            Err(vec![Unrendered::Named(Symbol::from("answer"))]),
            "precondition: a cache-loaded UserFn with no record is refused, not dropped"
        );

        // The backing `.cl` (the cache key) still holds the function source.
        let backing = "(defn answer [] 42)\n";
        let n = rehydrate(&st, &introspection, &module, backing);
        assert_eq!(n, 1, "exactly one UserFn rehydrated");

        // After rehydration, the function regenerates back into the source.
        let after = regen_ok(&st, Some(&introspection), &module);
        assert!(
            after.contains("answer"),
            "post-rehydration: UserFn is recovered into regenerated source: {after:?}"
        );
    }

    // -----------------------------------------------------------------------
    // S102 CS-D1 — origin-uniform regen dedup (Matrix B: single-authority)
    // -----------------------------------------------------------------------

    // Matrix B {defmacro (macro-expansion artifact) × single-authority}: a
    // macro-defining-macro turn records the ORIGINAL outer form under BOTH the
    // produced macro (`x`) and the produced defn (`x-def`). Regen MUST emit
    // that authored form exactly once and MUST NOT emit the expansion
    // artifact — persisting both was /port D1's directory poison (the pair
    // does not co-load).
    // spec: repl/spec/15-session-persistence.md §15.4 — rule 1 round trip;
    // §15.1 regeneration
    #[test]
    fn regen_macro_expansion_artifact_emits_authored_origin_once() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let expanded_defmacro =
            parse1("(defmacro x [] (macros/SexpList (macros/SCons x-def macros/SNil)))");
        install_macro(&mut st, "x", expanded_defmacro);
        install_userfn(&mut st, "x-def", 0, Vec::new());

        // One macro-call entry: both records carry the call at its position.
        let original = parse1("(mdef x 1)");
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        for name in ["x", "x-def"] {
            let fq = FQSymbol {
                module: module.clone(),
                symbol: name.into(),
            };
            let mut record = introspection.entry(fq).or_default();
            record.sexp = Some(original.clone());
            record.position = Some(AuthoredPosition::entered(0));
        }

        let out = regen_ok(&st, Some(&introspection), &module);
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

    // A user-typed `(begin (defn a …) (defn b …))` dissolves at entry: each
    // member records its own form at its own position, so each is written
    // once, in member order, and no `begin` is written.
    // spec: repl/spec/15-session-persistence.md §15.4 rules 1–2;
    // design/int/s125-binary-clean.md §4.2
    #[test]
    fn regen_writes_begin_members_as_their_own_entries() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_userfn(&mut st, "a", 0, Vec::new());
        install_userfn(&mut st, "b", 1, Vec::new());

        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        record_at(
            &introspection,
            &module,
            "b",
            "(defn b [] 2)",
            AuthoredPosition::entered(1),
        );
        record_at(
            &introspection,
            &module,
            "a",
            "(defn a [] 1)",
            AuthoredPosition::entered(0),
        );

        let out = regen_ok(&st, Some(&introspection), &module);
        assert_eq!(out, "(defn a [] 1)\n\n(defn b [] 2)\n");
    }

    // Two different forms recorded at one position are two entries, and
    // each is written: a position alone never drops a form.
    // spec: repl/spec/15-session-persistence.md §15.4 rule 1;
    // design/int/s125-binary-clean.md §4.2
    #[test]
    fn distinct_forms_at_one_position_are_each_written() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_userfn(&mut st, "a", 0, Vec::new());
        install_userfn(&mut st, "b", 1, Vec::new());
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let at = AuthoredPosition::in_file(7);
        record_at(&introspection, &module, "a", "(defn a [] 1)", at);
        record_at(&introspection, &module, "b", "(defn b [] 2)", at);

        let out = regen_ok(&st, Some(&introspection), &module);
        assert_eq!(out, "(defn a [] 1)\n\n(defn b [] 2)\n");
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
        install_userfn(&mut st, "f", 0, Vec::new());
        install_userfn(&mut st, "g", 1, Vec::new());
        let twice = parse1("(defmacro twice [e] (add-i64 e e))");
        install_macro(&mut st, "twice", twice.clone());

        // Distinct spans: parse the two defns from one source string.
        let sexps = cranelisp_frontend::parse("(defn f [] 1)\n(defn g [] 1)").unwrap();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "f".into(),
            })
            .or_default()
            .sexp = Some(sexps[0].clone());
        introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "g".into(),
            })
            .or_default()
            .sexp = Some(sexps[1].clone());
        introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "twice".into(),
            })
            .or_default()
            .sexp = Some(twice);

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(out.contains("(defn f [] 1)"), "f emitted: {out:?}");
        assert!(out.contains("(defn g [] 1)"), "g emitted: {out:?}");
        assert!(
            out.contains("(defmacro twice"),
            "direct defmacro emitted: {out:?}"
        );
    }

    // -----------------------------------------------------------------------
    // S102 CS-D2 — source-text-first emission (Matrix B: authorship fidelity)
    // -----------------------------------------------------------------------

    // The consistency gate is reader-desugar-aware: authored shorthand
    // re-parses to the recorded (desugared) sexp; garbage / stale / multi-form
    // sources fail.
    // spec: repl/spec/15-session-persistence.md §15.4 — rule 1, §15.1
    // (authorship fidelity)
    #[test]
    fn sexp_matches_source_desugar_aware_positive_and_negative_cells() {
        let shorthand = "(defmacro twice [e] `(add-i64 ~e ~e))";
        let desugared = parse1(shorthand); // parse desugars `~`/`` ` ``
        assert!(
            sexp_matches_source(&desugared, shorthand),
            "authored shorthand matches its own desugared parse"
        );
        assert!(
            !sexp_matches_source(&desugared, "(defn other [] 1)"),
            "a different form does not match"
        );
        assert!(
            !sexp_matches_source(&desugared, "garbage ("),
            "an unparseable source does not match"
        );
        assert!(
            !sexp_matches_source(&desugared, "(defn a [] 1) (defn b [] 2)"),
            "a multi-form source does not match"
        );
    }

    // S102 W5R M-5: the shared `verbatim_slice` gate slices a form's span out of
    // a text and returns it ONLY when it re-parses to the same form — the exact
    // behaviour both `process_form::verbatim_source_slice` and the introspection
    // rehydrator now route through (Principle 7). Positive: an in-bounds,
    // consistent slice returns byte-verbatim (reader shorthand preserved).
    // Negative: an out-of-bounds span and a stale/mismatched text return None.
    // spec: repl/spec/15-session-persistence.md §15.4 — rule 1, §15.1
    // (authorship fidelity)
    #[test]
    fn verbatim_slice_positive_and_negative_cells() {
        // The whole text is the single form — its span covers it exactly.
        let text = "(defmacro twice [e] `(add-i64 ~e ~e))";
        let form = parse1(text);
        assert_eq!(
            verbatim_slice(&form, text).as_deref(),
            Some(text),
            "an in-bounds, consistent slice returns the verbatim authored text"
        );

        // A form whose recorded span points past the end of a (shorter) text:
        // slice out of bounds → None → caller falls back to pretty_print.
        assert_eq!(
            verbatim_slice(&form, "(defmacro twice"),
            None,
            "an out-of-bounds span yields None"
        );

        // A form sliced against a DIFFERENT text of adequate length: the slice
        // is in-bounds but does not re-parse to the recorded form → None.
        let other = "(defn xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx [] 1)";
        assert!(other.len() >= text.len());
        assert_eq!(
            verbatim_slice(&form, other),
            None,
            "an in-bounds but inconsistent slice yields None"
        );
    }

    // Matrix B {file-originated hand-authored × authorship fidelity}: an entry
    // whose record carries the verbatim authored text emits it BYTE-EXACT —
    // reader shorthand preserved, never the desugared render (/port D2).
    // spec: repl/spec/15-session-persistence.md §15.4 — rule 1, §15.1
    // (authorship fidelity)
    #[test]
    fn regen_emits_verbatim_authored_source_reader_shorthand() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let authored = "(defmacro twice [e] `(add-i64 ~e ~e))";
        let desugared = parse1(authored);
        install_macro(&mut st, "twice", desugared.clone());

        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "twice".into(),
        };
        {
            let mut rec = introspection.entry(fq).or_default();
            rec.sexp = Some(desugared);
            rec.source = Some(authored.to_string());
        }

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(
            out.contains(authored),
            "the authored bytes are what gets written back (§15.4.7): {out:?}"
        );
        assert!(
            !out.contains("quasiquote"),
            "the desugared render must NOT replace the authored shorthand: {out:?}"
        );
    }

    // Negative: an INCONSISTENT recorded source (stale text that no longer
    // parses to the recorded sexp) falls back to the reconciled render —
    // verbatim emission can never corrupt the file.
    // spec: repl/spec.md §15.4 — invariant 1 (round-trip)
    #[test]
    fn regen_source_first_neg_inconsistent_source_falls_back_to_render() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_userfn(&mut st, "f", 0, Vec::new());

        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "f".into(),
        };
        {
            let mut rec = introspection.entry(fq).or_default();
            rec.sexp = Some(parse1("(defn f [x] (add-i64 x 1))"));
            rec.source = Some("stale garbage ( not the defn".to_string());
        }

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(
            out.contains("(defn f [x] (add-i64 x 1))"),
            "inconsistent source falls back to the sexp render: {out:?}"
        );
        assert!(
            !out.contains("garbage"),
            "the stale text never reaches the file: {out:?}"
        );
    }

    // Negative: a live `Def.docstring` edited out-of-band (set-doc / agent
    // Document-mode) makes the recorded source inconsistent — emission falls
    // back to the reconciled render carrying the LIVE docstring (§11.3a
    // authority preserved through the source-first path).
    // spec: design/int/session-persistence.md §11.3a
    #[test]
    fn regen_source_first_docstring_mismatch_falls_back_to_reconciled_render() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_userfn(&mut st, "f", 0, Vec::new());
        st.set_plain_callable_docstring(&Symbol::from("f"), "new doc".to_string())
            .expect("plain callable docstring fixture updates through funnel");

        let authored = "(defn f \"old doc\" [x] x)";
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "f".into(),
        };
        {
            let mut rec = introspection.entry(fq).or_default();
            rec.sexp = Some(parse1(authored));
            rec.source = Some(authored.to_string());
        }

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(
            out.contains("\"new doc\""),
            "the live docstring wins over the recorded source: {out:?}"
        );
        assert!(
            !out.contains("old doc"),
            "the stale docstring is dropped: {out:?}"
        );
    }

    // Positive twin: a recorded source that ALREADY carries the live docstring
    // is consistent and emits verbatim.
    // spec: design/int/session-persistence.md §11.3a
    #[test]
    fn regen_source_first_docstring_consistent_emits_verbatim() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_userfn(&mut st, "f", 0, Vec::new());
        st.set_plain_callable_docstring(&Symbol::from("f"), "the doc".to_string())
            .expect("plain callable docstring fixture updates through funnel");

        let authored = "(defn f \"the doc\" [x]    x)"; // authored spacing preserved
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "f".into(),
        };
        {
            let mut rec = introspection.entry(fq).or_default();
            rec.sexp = Some(parse1(authored));
            rec.source = Some(authored.to_string());
        }

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(
            out.contains(authored),
            "a docstring-consistent source emits byte-verbatim: {out:?}"
        );
    }

    // Rehydration captures the VERBATIM span slice off the backing file (it
    // holds the file text at that moment), never `pretty_print(sexp)` — the
    // reader-shorthand-loss half of /port D2's rehydration compounding.
    // spec: repl/spec/15-session-persistence.md §15.4 — rule 1, §15.1
    // (authorship fidelity)
    #[test]
    fn rehydrate_captures_verbatim_source_slice() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_userfn(&mut st, "g", 0, Vec::new());

        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        // Authored formatting a pretty-printer would not reproduce.
        let backing = ";; header\n(defn g [x]\n    (mul-i64 x   2))\n";
        let n = rehydrate(&st, &introspection, &module, backing);
        assert_eq!(n, 1);
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "g".into(),
        };
        assert_eq!(
            introspection.get(&fq).unwrap().source.as_deref(),
            Some("(defn g [x]\n    (mul-i64 x   2))"),
            "rehydrated source is the exact file slice"
        );
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
        assert_eq!(
            rendered, "(defn f [x] x)",
            "no-op when nothing to inject: {rendered:?}"
        );
        assert!(
            !rendered.contains("\"\""),
            "no spurious empty docstring: {rendered:?}"
        );
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
        assert_eq!(
            doc.as_deref(),
            Some("the doc"),
            "docstring recovered in slot"
        );
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
            cranelisp_types::ParsedEntry::Def {
                docstring,
                variants,
                ..
            } => {
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
        assert!(
            !rendered.contains("ignored"),
            "non-defn must be untouched: {rendered:?}"
        );
    }

    // End-to-end via `generate_module_source`: a UserFn whose live `Def.docstring`
    // is set but whose stored (introspection) sexp has NO docstring regenerates
    // WITH the docstring — the §17.15.3 durable promise at the regen seam.
    // spec: design/int/session-persistence.md §11.3a — set-doc persists via regen
    #[test]
    fn generate_module_source_emits_live_docstring() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_userfn(&mut st, "double", 0, Vec::new());
        st.set_plain_callable_docstring(
            &Symbol::from("double"),
            "doubles its argument".to_string(),
        )
        .expect("plain callable docstring fixture updates through funnel");
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "double".into(),
        };
        introspection.entry(fq).or_default().sexp = Some(parse1("(defn double [x] (add-i64 x x))"));

        let out = regen_ok(&st, Some(&introspection), &module);
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
        let recaptured =
            cranelisp_frontend::capture_module_preamble(&regen_source).expect("recaptured");
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
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.module_preamble = Some("Header doc\nsecond line".to_string());
        install_userfn(&mut st, "answer", 0, Vec::new());
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "answer".into(),
        };
        introspection.entry(fq).or_default().sexp = Some(parse1("(defn answer [] 42)"));

        let out = regen_ok(&st, Some(&introspection), &module);
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
        let out_none = regen_ok(&st, Some(&introspection), &module);
        assert!(
            !out_none.starts_with(";;"),
            "a no-preamble module must regenerate without a leading block: {out_none:?}"
        );
    }

    // -----------------------------------------------------------------------
    // FIXME 0549 — non-defining `__expr` forms are NOT persisted
    // -----------------------------------------------------------------------

    // A bare top-level expression is recorded as a synthetic `__expr`-named
    // `UserFn`. `generate_fns_and_macros` MUST suppress its SOURCE emission
    // (symmetric with the `$`-mangled filter), while leaving the live
    // in-session `__expr` symbol-table entry untouched — only emission is
    // suppressed, not the entry the reload path reads.
    // spec: repl/spec.md §15.7 — transient expressions are session-only
    #[test]
    fn regen_excludes_bare_expr_wrapper_keeps_defns() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        // The synthetic expression wrapper + a real user fn.
        install_userfn(&mut st, "__expr", 0, Vec::new());
        install_userfn(&mut st, "g", 1, Vec::new());

        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "__expr".into(),
            })
            .or_default()
            .source = Some("(add-i64 1 2)".to_string());
        introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "g".into(),
            })
            .or_default()
            .sexp = Some(parse1("(defn g [x] (mul-i64 x 2))"));

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(
            !out.contains("add-i64") && !out.contains("__expr"),
            "the transient `__expr` expression MUST NOT be persisted: {out:?}"
        );
        assert!(
            out.contains("(defn g"),
            "the real defn MUST be persisted: {out:?}"
        );

        // The live in-session entry is untouched — only its emission is
        // suppressed (the reload and cache-restore paths read this entry).
        assert!(
            st.get(&cranelisp_types::Symbol::from("__expr")).is_some(),
            "the live `__expr` symbol-table entry MUST remain after regeneration"
        );
    }

    // Data-loss edge (the over-broad-filter guard): the exclusion matches the
    // synthetic `__expr` wrapper EXACTLY, never as a prefix. A legitimate user
    // definition whose name merely STARTS WITH `__expr` (`__expr-helper`) is
    // real module content and MUST survive regeneration — an over-broad
    // `starts_with("__expr")` filter would silently drop it.
    // spec: repl/spec.md §15.7 — only the exact `__expr` wrapper is transient
    #[test]
    fn regen_preserves_user_defn_named_like_expr_wrapper() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        // A real user fn whose name starts with `__expr` but is NOT the wrapper.
        install_userfn(&mut st, "__expr-helper", 0, Vec::new());
        // The transient wrapper itself, for contrast.
        install_userfn(&mut st, "__expr", 1, Vec::new());

        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "__expr-helper".into(),
            })
            .or_default()
            .sexp = Some(parse1("(defn __expr-helper [] 1)"));
        introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "__expr".into(),
            })
            .or_default()
            .source = Some("(add-i64 1 2)".to_string());

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(
            out.contains("(defn __expr-helper [] 1)"),
            "a user defn named like the wrapper MUST be preserved (exact-match \
             filter, not prefix): {out:?}"
        );
        assert!(
            !out.contains("add-i64"),
            "the exact `__expr` wrapper's transient expression is still suppressed: {out:?}"
        );
    }

    // -----------------------------------------------------------------------
    // FIXME 0538 — source-first regen for §5–7 (traits/types)
    // -----------------------------------------------------------------------

    fn type_def_entry(module: &ModuleFullPath, type_name: &str) -> Binding<crate::code::Code> {
        use cranelisp_types::{FQTypeName, TypeDefInfo, Visibility};
        Binding::new(
            Decl::Type(TypeRecord::Defined {
                info: TypeDefInfo {
                    name: FQTypeName::new(module.clone(), type_name.into()),
                    type_params: vec![],
                    constructors: vec![],
                },
                docstring: None,
            }),
            Visibility::Public,
        )
    }

    fn trait_decl_entry(trait_name: &str) -> Binding<crate::code::Code> {
        use cranelisp_types::{TraitDeclInfo, Visibility};
        Binding::new(
            Decl::Trait(TraitRecord::new(
                TraitDeclInfo {
                    name: trait_name.into(),
                    type_params: vec![],
                    methods: vec![],
                },
                None,
            )),
            Visibility::Public,
        )
    }

    // Source-first: a `deftype` record carrying BOTH sexp and a non-canonically
    // formatted authored source that re-parses to the recorded sexp emits the
    // VERBATIM source byte-for-byte (formatting preserved), not the pretty-
    // printer's reflow.
    // spec: repl/spec/15-session-persistence.md §15.4 — rule 1, §15.1
    // (authorship fidelity), §5–7
    #[test]
    fn regen_type_decl_source_first_verbatim() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.install_binding("Pt".into(), type_def_entry(&module, "Pt"))
            .expect("type fixture installs");

        // Non-canonical spacing; re-parses to the recorded sexp.
        let authored = "(deftype   Pt (MkPt [:Int x]  [:Int y]))";
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let mut rec = introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "Pt".into(),
            })
            .or_default();
        rec.sexp = Some(parse1(authored));
        rec.source = Some(authored.to_string());
        drop(rec);

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(
            out.contains(authored),
            "a matching source MUST regenerate byte-verbatim (source-first): {out:?}"
        );
    }

    // Fallback: when the recorded source does NOT re-parse to the recorded sexp
    // (stale / mismatched), the pretty-printer render of the sexp is emitted —
    // never the stale source text.
    // spec: repl/spec/15-session-persistence.md §15.4 — rule 1, §15.1
    // (consistency gate), §5–7
    #[test]
    fn regen_type_decl_falls_back_to_pretty_on_source_mismatch() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.install_binding("Pt".into(), type_def_entry(&module, "Pt"))
            .expect("type fixture installs");

        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let mut rec = introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "Pt".into(),
            })
            .or_default();
        rec.sexp = Some(parse1("(deftype Pt (MkPt [:Int x] [:Int y]))"));
        // A stale source describing a DIFFERENT declaration.
        rec.source = Some("(deftype Stale (Other [:Int z]))".to_string());
        drop(rec);

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(
            out.contains("MkPt") && !out.contains("Stale"),
            "a mismatched source MUST fall back to the sexp render, never the \
             stale text: {out:?}"
        );
    }

    // REPL-defined decls record only the authored `Introspection.source` (no
    // sexp is captured for a `TypeDef`/`TraitDecl` form). Before FIXME 0538 the
    // sexp-only gate dropped them entirely; now the verbatim source is emitted
    // when it parses to a single form.
    // spec: repl/spec.md §15.4 — §5–7 source-only emission
    #[test]
    fn regen_trait_decl_source_only_emits() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.install_binding("Sizeable".into(), trait_decl_entry("Sizeable"))
            .expect("trait fixture installs");

        let authored = "(deftrait (Sizeable a) (size [a] Int))";
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "Sizeable".into(),
            })
            .or_default()
            .source = Some(authored.to_string()); // sexp intentionally None

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(
            out.contains(authored),
            "a REPL-defined trait (source-only record) MUST regenerate from its \
             verbatim authored source: {out:?}"
        );
    }

    // An entry that a section generator selects but cannot render, because it
    // has neither form nor text, refuses the whole generation and is named —
    // never silently dropped, never emitted as garbage. One cell per section
    // generator; the impl is reachable only through `written_trait_impls`.
    // spec: design/int/session-persistence.md §2.4.3, §12.3 row 3
    #[test]
    fn regen_refuses_each_kind_selected_without_a_record() {
        let module = ModuleFullPath::from("user");
        let refused = |st: &crate::code::SessionSymbolTable| {
            let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
            generate_module_source(st, Some(&introspection), &module)
                .map_err(|unrendered| unrendered.0)
        };

        let mut types = crate::code::SessionSymbolTable::new_with_params(module.clone());
        types
            .install_binding("Pt".into(), type_def_entry(&module, "Pt"))
            .expect("type fixture installs");
        assert_eq!(
            refused(&types),
            Err(vec![Unrendered::Named(Symbol::from("Pt"))])
        );

        let mut traits = crate::code::SessionSymbolTable::new_with_params(module.clone());
        traits
            .install_binding("Disp".into(), trait_decl_entry("Disp"))
            .expect("trait fixture installs");
        assert_eq!(
            refused(&traits),
            Err(vec![Unrendered::Named(Symbol::from("Disp"))])
        );

        let mut impls = crate::code::SessionSymbolTable::new_with_params(module.clone());
        upsert_written_impl(&mut impls, "lib", "Disp", &module, "W");
        let refusal = refused(&impls).expect_err("the impl has no record");
        assert_eq!(
            refusal,
            vec![Unrendered::Impl {
                trait_name: cranelisp_types::FQTraitName::new("lib".into(), "Disp".into()),
                impl_type: cranelisp_types::FQTypeName::new(module.clone(), "W".into()),
            }]
        );
        // The refusal names each half by its own module, from the settled pair.
        assert_eq!(
            UnrenderedEntries(refusal).to_string(),
            "`impl lib/Disp for user/W`"
        );

        let mut fns = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_userfn(&mut fns, "f", 0, Vec::new());
        assert_eq!(
            refused(&fns),
            Err(vec![Unrendered::Named(Symbol::from("f"))])
        );
    }

    // -----------------------------------------------------------------------
    // RT-4 — impl-source-regen close (session-persistence.md §12)
    // -----------------------------------------------------------------------

    fn install_trait_impl_shell(
        table: &mut crate::code::SessionSymbolTable,
        home: &ModuleFullPath,
        trait_name: &str,
        impl_type_module: &ModuleFullPath,
        impl_type: &str,
        impl_module: &ModuleFullPath,
    ) {
        use cranelisp_types::{FQTraitName, FQTypeName, Visibility, WrittenTraitImpl};
        let record = WrittenTraitImpl::new(
            FQTraitName::new(home.clone(), trait_name.into()),
            FQTypeName::new(impl_type_module.clone(), impl_type.into()),
            impl_module.clone(),
            vec!["dp".into()],
            Visibility::Public,
            format!("{trait_name}.{impl_type}").into(),
        );
        cranelisp_types::enrol_written_trait_impl(table, &record)
            .expect("trait impl shell fixture enrols through discovery funnel");
    }

    /// The introspection key an impl's live turn records its form under.
    fn impl_key(trait_home: &str, trait_name: &str, type_home: &str, impl_type: &str) -> Symbol {
        cranelisp_types::trait_impl_key(
            &cranelisp_types::FQTypeName::new(type_home.into(), impl_type.into()),
            &cranelisp_types::FQTraitName::new(trait_home.into(), trait_name.into()),
        )
    }

    fn record_impl_source(
        introspection: &DashMap<FQSymbol, Introspection>,
        writer: &ModuleFullPath,
        key: Symbol,
        source: &str,
    ) {
        introspection
            .entry(FQSymbol {
                module: writer.clone(),
                symbol: key,
            })
            .or_default()
            .source = Some(source.to_string());
    }

    // §12.3: an impl written in M — of M's own trait or an imported one — is
    // enumerated from M's written-impl record and rendered from the form its
    // live turn recorded under the settled pair's key.
    // spec: repl/spec.md §15.4 — `impl` is persisted module content.
    #[test]
    fn generate_impls_enumerates_each_impl_written_in_module() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        upsert_written_impl(&mut st, "user", "Disp", &module, "W");
        upsert_written_impl(&mut st, "lib.shape", "Area", &module, "W");
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let own = "(impl Disp W (defn dp [w] 42))";
        let imported = "(impl Area W (defn area [w] 1))";
        record_impl_source(
            &introspection,
            &module,
            impl_key("user", "Disp", "user", "W"),
            own,
        );
        record_impl_source(
            &introspection,
            &module,
            impl_key("lib.shape", "Area", "user", "W"),
            imported,
        );

        let out = regen_ok(&st, Some(&introspection), &module);
        assert_eq!(out, format!("{imported}\n\n{own}\n"), "{out:?}");
    }

    // §12.3 legal exclusion: a shell HOMED in M but WRITTEN IN another module N
    // has no record in M, so M's regeneration does not reach it, even with N's
    // form recorded.
    // spec: repl/spec.md §15.4; session-persistence.md §12.2 (D45-amended storage)
    #[test]
    fn generate_impls_excludes_impl_written_in_another_module() {
        let home = ModuleFullPath::from("user");
        let other = ModuleFullPath::from("other");
        let mut st = crate::code::SessionSymbolTable::new_with_params(home.clone());
        install_trait_impl_shell(&mut st, &home, "Disp", &other, "X", &other);
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        record_impl_source(
            &introspection,
            &other,
            impl_key("user", "Disp", "other", "X"),
            "(impl Disp X (defn dp [w] 7))",
        );

        let out = regen_ok(&st, Some(&introspection), &home);
        assert!(
            out.is_empty(),
            "an impl written in another module is a LEGAL exclusion from M's regen: {out:?}"
        );
    }

    // REPRO-1064's unit row and int §6.13's: a local `Box` and an imported `Box`
    // renamed to `B` are two impls of one trait in one module. The injective
    // key keeps them two, and both regenerate.
    // spec: design/int/int.md §6.13 — the identity is the settled pair, held injectively
    #[test]
    fn generate_impls_keeps_impls_for_same_named_types_distinct() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        upsert_labelled_impl(&mut st, "prelude", "Show", &module, "Box", "Show.Box");
        upsert_labelled_impl(
            &mut st,
            "prelude",
            "Show",
            &ModuleFullPath::from("lib"),
            "Box",
            "Show.B",
        );
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let local = "(impl Show Box (defn show [x] \"local\"))";
        let renamed = "(impl Show B (defn show [x] \"lib\"))";
        record_impl_source(
            &introspection,
            &module,
            impl_key("prelude", "Show", "user", "Box"),
            local,
        );
        record_impl_source(
            &introspection,
            &module,
            impl_key("prelude", "Show", "lib", "Box"),
            renamed,
        );

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(out.contains(local) && out.contains(renamed), "{out:?}");
    }

    // Rows 1 and 2 are gone: neither a dotted introspection record nor a shell
    // without its writer record names an impl to regenerate.
    // spec: design/int/int.md §6.13 — regeneration enumerates the records alone
    #[test]
    fn generate_impls_reads_no_identity_beside_the_records() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_trait_impl_shell(&mut st, &module, "Disp", &module, "W", &module);
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        record_impl_source(
            &introspection,
            &module,
            "Disp.W".into(),
            "(impl Disp W (defn dp [w] 42))",
        );

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(out.is_empty(), "{out:?}");
    }

    // -----------------------------------------------------------------------
    // Backing-file rehydration of every native definition form
    // (session-persistence.md §2.4.2) and the no-silent-omission refusal
    // (§2.4.3).
    // -----------------------------------------------------------------------

    fn rehydrate(
        st: &crate::code::SessionSymbolTable,
        introspection: &DashMap<FQSymbol, Introspection>,
        module: &ModuleFullPath,
        backing: &str,
    ) -> usize {
        rehydrate_introspection_from_source(st, introspection, module, backing)
    }

    /// Record an impl whose head was written bare, `(impl Trait Type …)`.
    fn upsert_written_impl(
        table: &mut crate::code::SessionSymbolTable,
        trait_home: &str,
        trait_name: &str,
        type_home: &ModuleFullPath,
        impl_type: &str,
    ) {
        let label = format!("{trait_name}.{impl_type}");
        upsert_labelled_impl(table, trait_home, trait_name, type_home, impl_type, &label);
    }

    fn upsert_labelled_impl(
        table: &mut crate::code::SessionSymbolTable,
        trait_home: &str,
        trait_name: &str,
        type_home: &ModuleFullPath,
        impl_type: &str,
        label: &str,
    ) {
        use cranelisp_types::{FQTraitName, FQTypeName, WrittenTraitImpl};
        let writer = table.path.clone();
        table
            .upsert_written_trait_impl(WrittenTraitImpl::new(
                FQTraitName::new(ModuleFullPath::from(trait_home), trait_name.into()),
                FQTypeName::new(type_home.clone(), impl_type.into()),
                writer,
                vec!["m".into()],
                Visibility::Public,
                label.into(),
            ))
            .expect("written-impl fixture records through the writer funnel");
    }

    const REHYDRATION_BACKING: &str = "\
(import [primitives [*]])
(deftype Shape (Circle [:Int r]) (Square [:Int s]))
(deftype Box [:Int v])
(deftrait Weigh (weigh [x] Int))
(impl Weigh Box (defn weigh [x] 1))
(impl Show Box (defn show [x] \"box\"))
(impl (Functor f) (Functor Option) (defn fmap [g o] o))
(defn- hidden [] 1)
(begin (defn a [] 1) (defn b [] 2))
(defmacro twice [e] `(add-i64 ~e ~e))
(defn retained-failure [] 1)
(impl Weigh Shape (defn weigh [x] 2))
(begin (deftype Token MkToken) (impl Weigh Token (defn weigh [x] 3)) (defn c [] 3))
";

    /// The members of the fixture's `begin` that fall in the type, impl and
    /// function sections.
    const SPANNING_MEMBERS: [&str; 3] = [
        "(deftype Token MkToken)",
        "(impl Weigh Token (defn weigh [x] 3))",
        "(defn c [] 3)",
    ];

    /// A cache-restored module: every live entry of the backing file's forms
    /// installed, no introspection records. `retained-failure` and the
    /// `Weigh Shape` impl are in the file but not live.
    fn rehydration_fixture() -> (ModuleFullPath, crate::code::SessionSymbolTable) {
        use cranelisp_types::{FQTypeName, TypeDefInfo};
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.install_binding("Shape".into(), type_def_entry(&module, "Shape"))
            .expect("sum type installs");
        let box_type = FQTypeName::new(module.clone(), "Box".into());
        install_callable(
            &mut st,
            "Box",
            0,
            Vec::new(),
            CallableOrigin::Ctor {
                type_name: box_type.clone(),
                tag: 0,
                field_count: 1,
                type_def: Some(Box::new(TypeDefInfo {
                    name: box_type,
                    type_params: vec![],
                    constructors: vec![],
                })),
            },
        );
        st.install_binding("Weigh".into(), trait_decl_entry("Weigh"))
            .expect("trait installs");
        install_trait_impl_shell(&mut st, &module, "Weigh", &module, "Box", &module);
        upsert_written_impl(&mut st, "user", "Weigh", &module, "Box");
        upsert_written_impl(&mut st, "prelude", "Show", &module, "Box");
        upsert_written_impl(
            &mut st,
            "prelude",
            "Functor",
            &ModuleFullPath::from("primitives"),
            "Option",
        );
        install_userfn(&mut st, "hidden", 1, Vec::new());
        install_userfn(&mut st, "a", 2, Vec::new());
        install_userfn(&mut st, "b", 3, Vec::new());
        install_macro(&mut st, "twice", parse1("(defmacro twice [e] e)"));
        st.install_binding("Token".into(), type_def_entry(&module, "Token"))
            .expect("spanning-begin type installs");
        upsert_written_impl(&mut st, "user", "Weigh", &module, "Token");
        install_userfn(&mut st, "c", 4, Vec::new());
        (module, st)
    }

    fn record_form(
        introspection: &DashMap<FQSymbol, Introspection>,
        module: &ModuleFullPath,
        key: &str,
    ) -> Option<String> {
        introspection
            .get(&FQSymbol {
                module: module.clone(),
                symbol: key.into(),
            })
            .and_then(|record| record.sexp.as_ref().map(Sexp::format_flat))
    }

    fn backing_form(prefix: &str) -> String {
        let form = cranelisp_frontend::parse(REHYDRATION_BACKING)
            .expect("fixture parses")
            .into_iter()
            .find(|form| form.format_flat().starts_with(prefix))
            .expect("fixture holds the form");
        form.format_flat()
    }

    // spec: design/int/session-persistence.md §2.4.2 — scope: sum and product
    // deftype and deftrait records come from the backing file, text verbatim.
    #[test]
    fn rehydrate_fills_declaration_records_from_backing_file() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);

        for (key, prefix) in [
            ("Shape", "(deftype Shape"),
            ("Box", "(deftype Box"),
            ("Weigh", "(deftrait Weigh"),
        ] {
            assert_eq!(
                record_form(&introspection, &module, key),
                Some(backing_form(prefix)),
                "`{key}` takes its authored form from the backing file"
            );
        }
        let box_source = introspection
            .get(&FQSymbol {
                module: module.clone(),
                symbol: "Box".into(),
            })
            .and_then(|record| record.source.clone());
        assert_eq!(box_source.as_deref(), Some("(deftype Box [:Int v])"));
    }

    // spec: design/int/int.md §6.13 — rehydration keys an impl form from the
    // one record carrying its authored label, including the HKT echo head, and
    // records it under that record's settled pair (own or imported trait).
    #[test]
    fn rehydrate_fills_impls_under_their_records_identity() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);

        for (key, prefix) in [
            (impl_key("user", "Weigh", "user", "Box"), "(impl Weigh Box"),
            (impl_key("prelude", "Show", "user", "Box"), "(impl Show Box"),
            (
                impl_key("prelude", "Functor", "primitives", "Option"),
                "(impl (Functor f)",
            ),
        ] {
            assert_eq!(
                record_form(&introspection, &module, key.as_ref()),
                Some(backing_form(prefix)),
                "impl `{key}` is rehydrated under its record's identity"
            );
        }
        assert_eq!(record_form(&introspection, &module, "Weigh.Box"), None);
    }

    // spec: design/int/int.md §6.13 — under a rename the authored label, not
    // the settled names, associates a form with its record: `(impl Show B …)`
    // with `B` renamed from `lib/Box` and a local `(impl Show Box …)` key to
    // their own records, and a qualified head stays apart from a bare one.
    #[test]
    fn rehydrate_keys_renamed_and_qualified_heads_to_their_own_records() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let lib = ModuleFullPath::from("lib");
        upsert_labelled_impl(&mut st, "prelude", "Show", &module, "Box", "Show.Box");
        upsert_labelled_impl(&mut st, "prelude", "Show", &lib, "Box", "Show.B");
        upsert_labelled_impl(&mut st, "prelude", "Eq", &lib, "Box", "Eq.lib/Box");
        upsert_labelled_impl(&mut st, "prelude", "Eq", &module, "Box", "Eq.Box");
        let backing = "\
(impl Show Box (defn show [x] \"local\"))
(impl Show B (defn show [x] \"lib\"))
(impl Eq lib/Box (defn = [x y] true))
(impl Eq Box (defn = [x y] false))
";
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        assert_eq!(rehydrate(&st, &introspection, &module, backing), 4);
        let source_of = |key: Symbol| {
            introspection
                .get(&FQSymbol {
                    module: module.clone(),
                    symbol: key,
                })
                .and_then(|record| record.source.clone())
        };
        assert_eq!(
            source_of(impl_key("prelude", "Show", "lib", "Box")).as_deref(),
            Some("(impl Show B (defn show [x] \"lib\"))")
        );
        assert_eq!(
            source_of(impl_key("prelude", "Show", "user", "Box")).as_deref(),
            Some("(impl Show Box (defn show [x] \"local\"))")
        );
        assert_eq!(
            source_of(impl_key("prelude", "Eq", "lib", "Box")).as_deref(),
            Some("(impl Eq lib/Box (defn = [x y] true))")
        );
        assert_eq!(
            source_of(impl_key("prelude", "Eq", "user", "Box")).as_deref(),
            Some("(impl Eq Box (defn = [x y] false))")
        );
        let out = regen_ok(&st, Some(&introspection), &module);
        assert_eq!(out.matches("(impl ").count(), 4, "{out}");
    }

    // spec: design/int/int.md §6.13 — a form matches exactly one record or
    // none: two records carrying one label leave the form unkeyed, and the
    // regeneration reports both rather than picking one. The one-record
    // control keys the form.
    #[test]
    fn rehydrate_leaves_a_form_whose_label_two_records_carry_unkeyed() {
        let module = ModuleFullPath::from("user");
        let backing = "(impl Show B (defn show [x] \"b\"))\n";
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        upsert_labelled_impl(
            &mut st,
            "prelude",
            "Show",
            &ModuleFullPath::from("lib"),
            "Box",
            "Show.B",
        );

        let control: DashMap<FQSymbol, Introspection> = DashMap::new();
        assert_eq!(
            rehydrate(&st, &control, &module, backing),
            1,
            "one record keys the form"
        );

        upsert_labelled_impl(
            &mut st,
            "prelude",
            "Show",
            &ModuleFullPath::from("alt"),
            "Box",
            "Show.B",
        );
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        assert_eq!(rehydrate(&st, &introspection, &module, backing), 0);
        assert!(introspection.is_empty(), "neither record is picked");
        let refusal = generate_module_source(&st, Some(&introspection), &module)
            .expect_err("both records are unrendered");
        assert_eq!(refusal.0.len(), 2, "{refusal}");
    }

    // spec: design/int/session-persistence.md §2.4.2; spec/09-macros.md §9.6
    // (the SHOULD leniency); design/int/s125-binary-clean.md §4.2 — scope:
    // private heads, and each member of a legacy file's `begin` takes its own
    // form, text and file position, as a load dissolves it.
    #[test]
    fn rehydrate_fills_private_heads_and_legacy_begin_members_with_their_own_forms() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);

        assert_eq!(
            record_form(&introspection, &module, "hidden"),
            Some(backing_form("(defn- hidden"))
        );
        assert_eq!(
            record_form(&introspection, &module, "a"),
            Some(parse1("(defn a [] 1)").format_flat())
        );
        assert_eq!(
            record_form(&introspection, &module, "b"),
            Some(parse1("(defn b [] 2)").format_flat())
        );
        let record = |key: &str| {
            introspection
                .get(&FQSymbol {
                    module: module.clone(),
                    symbol: key.into(),
                })
                .map(|record| (record.source.clone(), record.position))
                .expect("record filled")
        };
        let (a_source, a_at) = record("a");
        let (_, b_at) = record("b");
        assert_eq!(a_source.as_deref(), Some("(defn a [] 1)"));
        assert!(a_at.is_some() && a_at < b_at, "{a_at:?} {b_at:?}");
    }

    // spec: design/int/session-persistence.md §2.4.2 — a cache-restored macro
    // gets its authored form, not the published `macro_sexp`.
    #[test]
    fn rehydrate_gives_macro_its_authored_form() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);

        assert_eq!(
            record_form(&introspection, &module, "twice"),
            Some(backing_form("(defmacro twice"))
        );
    }

    // spec: design/int/session-persistence.md §2.4.2 liveness — a form whose
    // key names no live entry (a retained startup failure, an impl the table
    // does not record as written here) is not rehydrated.
    #[test]
    fn rehydrate_skips_forms_whose_key_is_not_live() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);

        assert_eq!(
            record_form(&introspection, &module, "retained-failure"),
            None
        );
        assert_eq!(
            record_form(
                &introspection,
                &module,
                impl_key("user", "Weigh", "user", "Shape").as_ref()
            ),
            None
        );
    }

    // spec: design/int/session-persistence.md §2.4.1–§2.4.2 absence — a REPL
    // declaration's text-only record is authoritative: the file may hold an
    // older generation, and rehydration must not replace it.
    #[test]
    fn rehydrate_keeps_authoritative_text_only_record() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let newer = "(deftrait Weigh (weigh [x] Int) (tare [x] Int))";
        let fq = FQSymbol {
            module: module.clone(),
            symbol: "Weigh".into(),
        };
        introspection.entry(fq.clone()).or_default().source = Some(newer.to_string());
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);

        let record = introspection.get(&fq).expect("record kept");
        assert_eq!(record.source.as_deref(), Some(newer));
        assert!(record.sexp.is_none(), "the older file form is not attached");
    }

    // spec: design/int/session-persistence.md §2.4.2 absence — a record
    // written by codegen alone carries no authored form and is filled.
    #[test]
    fn rehydrate_fills_clif_only_record() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: "hidden".into(),
            })
            .or_default()
            .clif_ir = Some("function u0:0() {}".to_string());
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);

        assert_eq!(
            record_form(&introspection, &module, "hidden"),
            Some(backing_form("(defn- hidden"))
        );
    }

    // spec: design/int/session-persistence.md §2.4.2 — an unparseable backing
    // file rehydrates nothing.
    #[test]
    fn rehydrate_unparseable_file_fills_nothing() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let broken = format!("{REHYDRATION_BACKING}(defn unclosed [] ");
        assert_eq!(rehydrate(&st, &introspection, &module, &broken), 0);
        assert!(introspection.is_empty());
    }

    // spec: design/int/session-persistence.md §2.4.3 negative;
    // design/int/s125-binary-clean.md §4.2 — a fully rehydrated module writes,
    // and the members of a legacy `begin`, in one section or across sections,
    // are each written once in member order with no `begin`.
    #[test]
    fn rehydrated_module_regenerates_every_definition() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);

        let out = regen_ok(&st, Some(&introspection), &module);
        for form in [
            "(deftype Shape (Circle [:Int r]) (Square [:Int s]))",
            "(deftype Box [:Int v])",
            "(deftrait Weigh (weigh [x] Int))",
            "(impl Weigh Box (defn weigh [x] 1))",
            "(impl Show Box (defn show [x] \"box\"))",
            "(impl (Functor f) (Functor Option) (defn fmap [g o] o))",
            "(defn- hidden [] 1)",
            "(defmacro twice [e] `(add-i64 ~e ~e))",
        ] {
            assert!(out.contains(form), "`{form}` regenerates: {out}");
        }
        assert!(!out.contains("(begin"), "{out}");
        for member in SPANNING_MEMBERS
            .iter()
            .chain(&["(defn a [] 1)", "(defn b [] 2)"])
        {
            assert_eq!(out.matches(member).count(), 1, "`{member}`: {out}");
        }
        // Authored order (repl §15.4 rule 2): the file's own order, the
        // spanning `begin`'s members last, in member order.
        let positions: Vec<usize> = [
            "(deftype Shape",
            "(deftype Box",
            "(deftrait Weigh",
            "(impl Weigh Box",
            "(defn- hidden",
            "(defn a [] 1)",
            "(defn b [] 2)",
            "(defmacro twice",
        ]
        .into_iter()
        .chain(SPANNING_MEMBERS)
        .map(|form| out.find(form).unwrap_or_else(|| panic!("{form} in {out}")))
        .collect();
        assert!(
            positions.windows(2).all(|pair| pair[0] < pair[1]),
            "emitted in the file's order: {out}"
        );
        assert!(!out.contains("retained-failure") && !out.contains("Weigh Shape"));
    }

    // spec: repl/spec/15-session-persistence.md §15.4 rules 1–2;
    // design/int/s125-binary-clean.md §4.2 — a REPL turn's `begin` spanning
    // sections dissolves at entry: the type, the `impl` and the function each
    // record their own member at consecutive entered positions, and each is
    // written once, in member order, with no `begin`.
    #[test]
    fn regen_repl_begin_spanning_sections_writes_each_member_once() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let weigh_token = impl_key("user", "Weigh", "user", "Token");
        for (sequence, (key, member)) in [
            ("Token", SPANNING_MEMBERS[0]),
            (weigh_token.as_ref(), SPANNING_MEMBERS[1]),
            ("c", SPANNING_MEMBERS[2]),
        ]
        .into_iter()
        .enumerate()
        {
            record_at(
                &introspection,
                &module,
                key,
                member,
                AuthoredPosition::entered(sequence as u64),
            );
        }
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);

        let out = regen_ok(&st, Some(&introspection), &module);
        assert!(!out.contains("(begin"), "{out}");
        let at: Vec<usize> = SPANNING_MEMBERS
            .iter()
            .map(|member| {
                assert_eq!(out.matches(member).count(), 1, "`{member}`: {out}");
                out.find(member).unwrap_or_default()
            })
            .collect();
        assert!(at.windows(2).all(|pair| pair[0] < pair[1]), "{out}");
    }

    // spec: design/int/session-persistence.md §2.4.3 — detection proof: remove
    // one rehydrated record and the refusal names exactly that entry.
    #[test]
    fn regen_refuses_when_a_rehydrated_record_is_removed() {
        let (module, st) = rehydration_fixture();
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        rehydrate(&st, &introspection, &module, REHYDRATION_BACKING);
        introspection.remove(&FQSymbol {
            module: module.clone(),
            symbol: impl_key("prelude", "Show", "user", "Box"),
        });

        let refusal = generate_module_source(&st, Some(&introspection), &module)
            .expect_err("a missing record refuses the generation");
        assert_eq!(
            refusal.to_string(),
            "`impl prelude/Show for user/Box`",
            "the warning names the entry"
        );
    }

    // -----------------------------------------------------------------------
    // S125 — the section selector (§4.1) and authored order (§4.2)
    // (design/int/s125-binary-clean.md)
    // -----------------------------------------------------------------------

    // One row per declaration class the fixtures can build: each classified
    // with its reason, the instance and internal names before any facet.
    // spec: repl/spec/15-session-persistence.md §15.4 rule 1;
    // design/int/s125-binary-clean.md §4.1
    #[test]
    fn selector_classifies_each_declaration_class() {
        use cranelisp_types::{FQTypeName, TypeDefInfo};
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        install_userfn(&mut st, "f", 0, Vec::new());
        install_userfn(&mut st, "__expr", 1, Vec::new());
        let product = FQTypeName::new(module.clone(), "Pt".into());
        install_callable(
            &mut st,
            "Pt",
            2,
            Vec::new(),
            CallableOrigin::Ctor {
                type_name: product.clone(),
                tag: 0,
                field_count: 1,
                type_def: Some(Box::new(TypeDefInfo {
                    name: product,
                    type_params: vec![],
                    constructors: vec![],
                })),
            },
        );
        install_callable(
            &mut st,
            "Leaf",
            3,
            Vec::new(),
            CallableOrigin::Ctor {
                type_name: FQTypeName::new(module.clone(), "Tree".into()),
                tag: 0,
                field_count: 0,
                type_def: None,
            },
        );
        install_macro(&mut st, "m", parse1("(defmacro m [] 1)"));
        st.install_binding("Tree".into(), type_def_entry(&module, "Tree"))
            .expect("type fixture installs");
        st.install_binding("Disp".into(), trait_decl_entry("Disp"))
            .expect("trait fixture installs");
        install_trait_impl_shell(&mut st, &module, "Disp", &module, "Tree", &module);

        let class = |name: &str| persistence(name, st.get(name).expect("fixture installed"));
        use Persistence::{Excluded, Persisted};
        assert_eq!(class("f"), Persisted(PersistedKind::Function));
        assert_eq!(class("__expr"), Excluded(Exclusion::Internal));
        assert_eq!(class("Pt"), Persisted(PersistedKind::Type));
        assert_eq!(class("Leaf"), Excluded(Exclusion::Constructor));
        assert_eq!(class("m"), Persisted(PersistedKind::Macro));
        assert_eq!(class("Tree"), Persisted(PersistedKind::Type));
        assert_eq!(class("Disp"), Persisted(PersistedKind::Trait));
        let shell = st
            .all_symbols()
            .find(|(_, entry)| matches!(entry.declaration, Decl::ImplShell(_)))
            .map(|(name, entry)| persistence(name.as_ref(), entry));
        // A shell's key is an internal name, so it is excluded by name first.
        assert!(matches!(shell, Some(Excluded(_))), "{shell:?}");
    }

    /// Record `form` for `name` at `position`.
    fn record_at(
        introspection: &DashMap<FQSymbol, Introspection>,
        module: &ModuleFullPath,
        name: &str,
        form: &str,
        position: AuthoredPosition,
    ) {
        let mut record = introspection
            .entry(FQSymbol {
                module: module.clone(),
                symbol: name.into(),
            })
            .or_default();
        record.sexp = Some(parse1(form));
        record.source = Some(form.to_string());
        record.position = Some(position);
    }

    // File positions keep the file's order, entered positions follow them in
    // entry order, and a record moved just after another stands between it
    // and the next; kind and name decide nothing.
    // spec: repl/spec/15-session-persistence.md §15.4 rule 2;
    // design/int/s125-binary-clean.md §4.2
    #[test]
    fn definitions_follow_authored_positions() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        for (slot, name) in ["a", "b", "c", "d"].iter().enumerate() {
            install_userfn(&mut st, name, slot, Vec::new());
        }
        st.install_binding("T".into(), type_def_entry(&module, "T"))
            .expect("type fixture installs");
        let introspection: DashMap<FQSymbol, Introspection> = DashMap::new();
        let file = AuthoredPosition::in_file;
        record_at(
            &introspection,
            &module,
            "d",
            "(defn d [] 4)",
            AuthoredPosition::entered(0),
        );
        record_at(&introspection, &module, "T", "(deftype T K)", file(30));
        record_at(&introspection, &module, "c", "(defn c [] 3)", file(5));
        record_at(
            &introspection,
            &module,
            "a",
            "(defn a [] 1)",
            file(30).just_after(),
        );
        record_at(&introspection, &module, "b", "(defn b [] 2)", file(50));
        let out = regen_ok(&st, Some(&introspection), &module);
        assert_eq!(
            out,
            "(defn c [] 3)\n\n(deftype T K)\n\n(defn a [] 1)\n\n(defn b [] 2)\n\n(defn d [] 4)\n"
        );
    }

    // Rule 4: platforms, submodules, exports, then imports, whatever order the
    // table holds them in.
    // spec: repl/spec/15-session-persistence.md §15.4 rule 4
    #[test]
    fn structural_sections_follow_rule_four() {
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        st.imports.push(import_spec(
            "lib",
            names(&[ImportEntry::Name {
                source: "x".into(),
                local: "x".into(),
            }]),
        ));
        st.exports.push(export_spec(
            "lib",
            names(&[ImportEntry::Name {
                source: "x".into(),
                local: "x".into(),
            }]),
        ));
        st.submodules.push(ModDecl {
            name: "sub".into(),
            visibility: cranelisp_types::Visibility::Public,
            inline_body: None,
            span: Span::SYNTHETIC,
        });
        st.platforms.push(PlatformSpec {
            name: "stdio".to_string(),
            span: Span::SYNTHETIC,
        });
        let out = regen_ok(&st, None, &module);
        let at = |needle: &str| {
            out.find(needle)
                .unwrap_or_else(|| panic!("{needle}: {out}"))
        };
        assert!(
            at("(platform") < at("(mod sub)")
                && at("(mod sub)") < at("(export")
                && at("(export") < at("(import"),
            "{out}"
        );
    }
}
