// REPL introspection-display `_doc` producer family — the coherent sibling of
// `src/display.rs`. Extracted from `repl.rs` per `design/int/repl-decomposition.md`
// §1.2 (S110, FIXME 0606). Pure relocation, behaviour-invariant.


use super::*;


/// Format the `/mem` snapshot (no-expression form).
///
/// Reads the current allocation counters from `cranelisp-intrinsics` and
/// returns a two-line report: one data line with current live bytes, and
/// a comment line with total alloc / dealloc counts and the currently-live
/// allocation count (`allocs - deallocs`).
pub(crate) fn format_mem_snapshot() -> String {
    let allocs = cranelisp_intrinsics::alloc_count();
    let deallocs = cranelisp_intrinsics::dealloc_count();
    let bytes_live = cranelisp_intrinsics::bytes_current();
    let live = allocs.saturating_sub(deallocs);
    format!(
        "; live: {bytes_live} bytes ({live} allocations)\n; allocs: {allocs}  deallocs: {deallocs}"
    )
}

// ===========================================================================
// §10.3 introspection-line span helpers (the `:Type module/name ; metadata`
// envelope). Every introspection producer builds a `StyledDoc` through these,
// so the R4 type annotation / R7 module prefix / R6 metadata roles are assigned
// once at construction; `render` (the seam) applies the styles once. Colour-off
// the concatenated span text is byte-identical to the pre-Wave-D plain lines.
// ===========================================================================

/// Push a `:Type` annotation as one R4 span (the leading `:` included).
pub(crate) fn push_type_annotation(doc: &mut StyledDoc, type_str: &str) {
    doc.push(Role::TypeAnnotation, format!(":{type_str}"));
}

/// Push a fully-qualified `module/name` — R7 dim `module/` prefix + R15 name.
pub(crate) fn push_fq_name(doc: &mut StyledDoc, module: &ModuleFullPath, name: &str) {
    doc.push(Role::ModulePrefix, format!("{module}/"));
    doc.plain(name);
}

/// Push a REPL structured-metadata `;` suffix/line as one R6 span.
pub(crate) fn push_metadata(doc: &mut StyledDoc, text: impl Into<String>) {
    doc.push(Role::ReplMetadata, text);
}

/// Push a `; warning: <message>` line (§10.3 K9): the `; warning: ` prefix is R6
/// metadata (dim), the message body is R11 warning detail (yellow), terminated by a
/// `\n`. The single builder for the warning-line role composition so it is
/// single-sourced (Principle 7) and unit-pinnable.
pub(crate) fn push_warning_line(doc: &mut StyledDoc, message: &str) {
    push_metadata(doc, "; warning: ");
    doc.push(Role::WarnDetail, message.to_string());
    doc.plain("\n");
}

/// A `; header\n<code>` block — the R6 metadata header line over a code `StyledDoc`
/// (the `/source`/`/sexp` framing).
pub(crate) fn code_block_doc(header: &str, code: StyledDoc) -> StyledDoc {
    let mut doc = StyledDoc::new();
    push_metadata(&mut doc, header);
    doc.plain("\n");
    doc.extend(code);
    doc
}

/// Build the `; classification[ - docstring]` metadata string (the R6 comment).
fn classification_metadata(classification: &str, docstring: Option<&str>) -> String {
    append_docstring_comment(format!("; {classification}"), docstring)
}

/// Format an overloaded (multi-sig) function as one line per variant, with
/// fully-qualified `module/name` per spec §4.1.1. Used by bare-symbol display
/// (`format_def_entry`).
///
/// First line carries the `; defn` classification + optional docstring; subsequent
/// variant lines carry only the type and qualified name. See repl/spec.md §1.3
/// + §4.1.1 and design/int/multi-sig-introspection.md.
#[cfg(test)]
pub(crate) fn format_overloaded_variants(
    name: &str,
    module: &ModuleFullPath,
    variants: &[OverloadVariant],
    docstring: Option<&str>,
) -> String {
    render(&format_overloaded_variants_doc(name, module, variants, docstring))
}

pub(crate) fn format_overloaded_variants_doc(
    name: &str,
    module: &ModuleFullPath,
    variants: &[OverloadVariant],
    docstring: Option<&str>,
) -> StyledDoc {
    let mut doc = StyledDoc::new();
    for (i, v) in variants.iter().enumerate() {
        if i > 0 {
            doc.plain("\n");
        }
        let fn_ty = Type::Fn(v.param_types.clone(), Box::new(v.ret_type.clone()));
        let type_str = format_type_qualified(&fn_ty);
        push_type_annotation(&mut doc, &type_str);
        doc.plain(" ");
        push_fq_name(&mut doc, module, name);
        if i == 0 {
            doc.plain(" ");
            push_metadata(&mut doc, classification_metadata("defn", docstring));
        }
    }
    doc
}

/// Free-function core of [`CompilerSession::collect_related`] (FIXME 0194),
/// taking the symbol tables + resolution scope explicitly so the cross-ref
/// projection is unit-testable without constructing a full `CompilerSession`
/// (`src/CLAUDE.md` testability discipline; mirrors the `worker::layout_hash_gate`
/// / `splice_inline_mod_to_bare` extractions). See the method docstring for the
/// per-category cross-ref rules.
pub(crate) fn collect_related_for(
    tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    scope: &ModuleFullPath,
    entry: &ModuleEntry<crate::code::Code>,
    fq: &FQSymbol,
    resolved_module: &ModuleFullPath,
) -> Vec<FQSymbol> {
    let mut related: Vec<FQSymbol> = Vec::new();
    // Helper: resolve a bare name to its home module (chain-follow); skip if
    // unreachable.
    let fq_at_home = |name: &str| -> Option<FQSymbol> {
        cranelisp_types::resolve_terminal_entry_and_home(tables, scope, name).map(
            |(_, home)| FQSymbol { module: home, symbol: Symbol::from(name) },
        )
    };
    match entry {
        // A `TypeDef` is a type → its constructors are the match arms.
        ModuleEntry::TypeDef { info, .. } => {
                for ctor in &info.constructors {
                    related.push(FQSymbol {
                        module: resolved_module.clone(),
                        symbol: ctor.clone(),
                    });
                }
            }
            // A `Constructor` Def → its parent type (defn-related). A product
            // ctor additionally carries the type facet's constructors.
            ModuleEntry::Def { kind, .. } => {
                if let DefKind::Constructor { type_name, type_def, .. } = kind.as_ref() {
                    related.push(FQSymbol {
                        module: type_name.module.clone(),
                        symbol: Symbol::from(type_name.name.as_ref()),
                    });
                    if let Some(td) = type_def {
                        for ctor in &td.constructors {
                            related.push(FQSymbol {
                                module: resolved_module.clone(),
                                symbol: ctor.clone(),
                            });
                        }
                    }
                }
            }
            // A `TraitDecl` → its method defns + its implementing types.
            ModuleEntry::TraitDecl { .. } => {
                let tn = TraitName::from(fq.symbol.as_ref());
                if let Some(decl) = cranelisp_types::lookup_trait_decl_chain(tables, scope, &tn) {
                    for m in &decl.methods {
                        related.push(FQSymbol {
                            module: resolved_module.clone(),
                            symbol: m.name.clone(),
                        });
                    }
                }
                for ty in cranelisp_types::get_implementing_types_chain(tables, scope, &tn) {
                    if let Some(fq) = fq_at_home(ty.as_ref()) {
                        related.push(fq);
                    }
                }
            }
            _ => {}
        }
        related
}

// =============================================================================
// Display formatting helpers (ported from repl/commands.rs)
// =============================================================================

/// Format a special form for display (spec §4.1.5).
///
/// The `:Type` prefix is rendered from the SpecialForm entry's own `scheme`
/// (the SINGLE SOURCE — registered in `bootstrap::register_special_forms`),
/// retiring the former hardcoded `match name { … }` sig table (FIXME 0338,
/// Principle 7). A scheme whose top type is a `Fn` produces the prefix; any
/// other shape (defensive — should not occur for a registered form) omits it.
pub(crate) fn format_special_form_display(
    name: &str,
    scheme: &Scheme,
    description: &str,
) -> String {
    render(&format_special_form_display_doc(name, scheme, description))
}

pub(crate) fn format_special_form_display_doc(
    name: &str,
    scheme: &Scheme,
    description: &str,
) -> StyledDoc {
    let mut doc = StyledDoc::new();
    if matches!(scheme.ty, Type::Fn(..)) {
        let type_str = format_type_qualified(&scheme.ty);
        push_type_annotation(&mut doc, &type_str);
        doc.plain(" ");
    }
    // A special form's subject is a bare `name` (no module qualifier), R15.
    doc.plain(name);
    doc.plain(" ");
    push_metadata(&mut doc, format!("; special form - {description}"));
    doc
}

/// Format a macro for display (spec §4.1.6).
#[cfg(test)]
pub(crate) fn format_macro_display(
    name: &str,
    clauses: &[MacroClauseInfo],
    docstring: Option<&str>,
    module: &ModuleFullPath,
) -> String {
    render(&format_macro_display_doc(name, clauses, docstring, module))
}

pub(crate) fn format_macro_display_doc(
    name: &str,
    clauses: &[MacroClauseInfo],
    docstring: Option<&str>,
    module: &ModuleFullPath,
) -> StyledDoc {
    let mut doc = StyledDoc::new();
    push_type_annotation(&mut doc, &format!("{module}/{name}"));
    doc.plain(" ");
    push_metadata(&mut doc, append_docstring_comment("; defmacro".to_string(), docstring));
    for clause in clauses {
        let params = format_macro_clause_params(clause);
        doc.plain("\n");
        push_metadata(&mut doc, format!("; {params} -> Sexp"));
    }
    // repl/spec.md §11.2.2: a multi-clause macro card ends with a clause-count
    // summary line (two leading spaces, no `;`). The single-clause worked
    // example (`/info when`) shows NO count line, so gate on `> 1`. The count
    // is always >= 2 under this gate, so a fixed "clauses" is correct.
    if clauses.len() > 1 {
        doc.plain(format!("\n  {} clauses", clauses.len()));
    }
    doc
}

/// Format macro clause parameters as `[param1 param2 ...]`.
pub(crate) fn format_macro_clause_params(clause: &MacroClauseInfo) -> String {
    let mut parts = Vec::new();
    for param in &clause.params {
        match param {
            MacroParam::Name(name) => parts.push(name.to_string()),
            MacroParam::Bracket { fixed, rest } => {
                let mut inner: Vec<String> = fixed.iter().map(|f| f.to_string()).collect();
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

/// Format a related symbols section (spec §1.1). The symbol block uses the
/// shared §3.3 layout formatter (repl/spec.md:198 — related lists use the same
/// normative L0–L4 layout as `/list`), rendered as comment rows.
/// The `StyledDoc` for a related-symbol section — the drawer header AND its name
/// bodies are all R6 metadata (§10.3 R6); the `\n` line breaks stay Plain.
pub(crate) fn format_related_section_doc(label: &str, names: &[&str]) -> StyledDoc {
    let owned: Vec<String> = names.iter().map(|n| n.to_string()).collect();
    let mut doc = StyledDoc::new();
    doc.plain("\n");
    push_metadata(&mut doc, format!("; {label}:"));
    for row in format_symbol_layout(&owned) {
        doc.plain("\n");
        push_metadata(&mut doc, format!(";  {row}"));
    }
    doc
}

#[cfg(test)]
pub(crate) fn format_trait_related_sections(
    method_names: &[&str],
    impl_type_names: &[&str],
    full_impl_section: bool,
) -> String {
    render(&format_trait_related_sections_doc(
        method_names,
        impl_type_names,
        full_impl_section,
    ))
}

pub(crate) fn format_trait_related_sections_doc(
    method_names: &[&str],
    impl_type_names: &[&str],
    full_impl_section: bool,
) -> StyledDoc {
    let mut doc = StyledDoc::new();
    if !method_names.is_empty() {
        doc.extend(format_related_section_doc("defn", method_names));
    }
    if full_impl_section || !impl_type_names.is_empty() {
        doc.extend(format_related_section_doc("impl", impl_type_names));
    }
    doc
}

/// Indent every line of a rendered definition source by two spaces — the
/// `/info` block layout (`repl/spec.md` §3.6 worked example; the §18.4
/// broken-symbol example uses the same indentation).
pub(crate) fn indent_source_block(text: &str) -> String {
    text.lines()
        .map(|l| format!("  {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Maximum number of names per body row in the breaking layout (L2/L3/L4).
const LAYOUT_ROW_CAP: usize = 6;

/// Threshold (exclusive) below which a category renders on a single line (L0/L1).
/// Fewer than 7 names → single line; 7 or more → breaking layout.
const LAYOUT_BREAK_THRESHOLD: usize = 7;

/// The single normative symbol-layout formatter shared by `/list` (§3.3),
/// `/imports` (§3.4), `/exports` (§3.5), and related-symbol lists (§2).
///
/// Realises rules L0–L4 from repl/spec.md §3.3. Returns the BODY rows (names
/// only, no indent, no `: type` suffix) in order; callers add their own chrome
/// (the `Label:` header and two-space indent). The same name set MUST always
/// produce byte-for-byte identical output across all four commands.
///
/// - **L0/L1** — fewer than 7 names → a single space-separated row; 7+ break.
/// - **L2** — operators first, on their own rows, capped at 6/row; an operator
///   never shares a row with an alphabetic name.
/// - **L3** — alphabetic names grouped by first letter (case-insensitive) in
///   sorted order; a group flushes the current row when `count + size > 6`, so
///   a group never straddles a row boundary…
/// - **L4** — …except a single group of more than 6 names, which hard-wraps at
///   6/row within itself.
pub(crate) fn format_symbol_layout(names: &[String]) -> Vec<String> {
    if names.is_empty() {
        return Vec::new();
    }

    // Deterministic input ordering (callers already sort, but the formatter is
    // the single source of truth for the contract — sort defensively).
    let mut sorted: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
    sorted.sort();

    // L0/L1: below the threshold, one space-separated row, no breaking.
    if sorted.len() < LAYOUT_BREAK_THRESHOLD {
        return vec![sorted.join(" ")];
    }

    let mut rows: Vec<String> = Vec::new();

    // L2: operators first, on their own rows, capped at LAYOUT_ROW_CAP per row.
    // After the last operator a new row starts — operators never share a row
    // with an alphabetic name.
    let operators: Vec<&str> = sorted.iter().copied().filter(|n| is_operator_name(n)).collect();
    for chunk in operators.chunks(LAYOUT_ROW_CAP) {
        rows.push(chunk.join(" "));
    }

    // L3/L4: alphabetic names grouped by first letter (case-insensitive), in
    // sorted order. Build the contiguous letter groups (input is sorted, so
    // names sharing a first letter are already adjacent).
    let mut groups: Vec<Vec<&str>> = Vec::new();
    let mut current_letter: Option<char> = None;
    for name in sorted.iter().copied().filter(|n| !is_operator_name(n)) {
        let letter = name.chars().next().map(|c| c.to_ascii_lowercase());
        if letter != current_letter {
            current_letter = letter;
            groups.push(Vec::new());
        }
        if let Some(g) = groups.last_mut() {
            g.push(name);
        }
    }

    let mut row: Vec<&str> = Vec::new();
    for group in &groups {
        if group.len() > LAYOUT_ROW_CAP {
            // L4: an oversized single-letter group hard-wraps at 6/row. Flush
            // any in-progress row first so the group starts fresh.
            if !row.is_empty() {
                rows.push(row.join(" "));
                row.clear();
            }
            for chunk in group.chunks(LAYOUT_ROW_CAP) {
                rows.push(chunk.join(" "));
            }
            continue;
        }
        // L3: early-break to keep the group whole.
        if !row.is_empty() && row.len() + group.len() > LAYOUT_ROW_CAP {
            rows.push(row.join(" "));
            row.clear();
        }
        row.extend(group.iter().copied());
    }
    if !row.is_empty() {
        rows.push(row.join(" "));
    }

    rows
}

/// Emit the shared §3.3 L0–L4 layout rows for `names`, each indented two
/// spaces (the `/list` / `/imports` / `/exports` body format). Single-sources
/// the layout body used by both `append_name_category` and the `/imports`
/// "Prelude (implicit)" group (FIXME 0546 — the prelude group formerly dumped
/// one name per line, bypassing `format_symbol_layout`; routing both through
/// this helper is the Principle-7 fix).
fn append_layout_body(buf: &mut String, names: &[String]) {
    for row in format_symbol_layout(names) {
        buf.push_str("  ");
        buf.push_str(&row);
        buf.push('\n');
    }
}

/// Append a category of names to a string buffer (for /list, /imports, /exports),
/// rendering the symbol block through the shared §3.3 layout formatter.
pub(crate) fn append_name_category(buf: &mut String, label: &str, names: &[String]) {
    if names.is_empty() {
        return;
    }
    // §10.3 R12 (Header) — the category header (`Fns:`, `Types:`, …) is bold; the
    // name bodies stay default-styled layout (the scope boundary, §10.3). Rendered
    // through the seam so colour-off the bytes are unchanged.
    buf.push_str(&render(&StyledDoc::span(Role::Header, format!("{label}:"))));
    buf.push('\n');
    append_layout_body(buf, names);
}

/// Build the `/imports` "Prelude (implicit)" group (spec §3.4). The header line
/// carries a trailing suffix comment explaining the outer-scope semantics; the
/// prelude names render through the SAME shared §3.3 L0–L4 layout as every
/// other `/imports` category (FIXME 0546). The header suffix comment is
/// preserved verbatim — the layout applies only to the name body. Extracted as
/// a free function so the header-preservation + shared-layout routing is
/// unit-testable without a `CompilerSession`.
pub(crate) fn format_prelude_implicit_group(names: &[String]) -> String {
    let mut out = String::from(
        "Prelude (implicit):  \
         ; available via the prelude outer scope; a local def or a clashing \
         import of the same name conflicts — use the fully-qualified name\n",
    );
    append_layout_body(&mut out, names);
    out
}

/// Format a Sexp value as a readable string.
pub(crate) fn format_sexp(sexp: &Sexp) -> String {
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
        Sexp::Comment(text, _) => {
            if text.is_empty() {
                ";".to_string()
            } else {
                format!("; {text}")
            }
        }
    }
}

/// Append docstring as a comment suffix.
pub(crate) fn append_docstring_comment(base: String, docstring: Option<&str>) -> String {
    match docstring {
        Some(doc) if !doc.is_empty() => {
            let first_line = doc.lines().next().unwrap_or("");
            if first_line.is_empty() {
                base
            } else {
                format!("{base} - {first_line}")
            }
        }
        _ => base,
    }
}

impl CompilerSession {
    /// REPL `/info NAME` — one-shot description of a symbol resolved from
    /// `name` against the current REPL module. Returns the symbol's
    /// classification (Fn / Type / Trait / Macro / Constructor / SpecialForm),
    /// scheme (if applicable), docstring, and the captured source text.
    ///
    /// Pure read against `shared.symbol_tables` + `shared.introspection`.
    /// Returns `None` if the bare `name` does not resolve in the current
    /// module (no chain-follow performed at this layer — the caller may
    /// chain-follow if it wants imports + reexports resolved).
    pub fn describe_symbol(&self, name: &str) -> Option<SymbolDescription> {
        // Probe current module first, then the prelude outer-scope hop, then
        // root `""` (FIXME 0192 Residual Task 3 + FIXME 0193 — special-form
        // metadata lives at root, not in user-mode tables; S78 §2.7.6 — prelude
        // hop). Routes through the canonical `lookup_with_prelude_fallback`
        // (root tier ON) so the three-tier walk has a single definition
        // (S87 §4 dedup, Principle 7). The resolved module reflects where the
        // entry actually lives so the returned `FQSymbol` is correct.
        let (entry, resolved_module) = self.lookup_with_prelude_fallback(name)?;
        let fq = FQSymbol {
            module: resolved_module.clone(),
            symbol: Symbol::from(name),
        };
        // Bucketing is the shared `classify_listing_entry` classifier (FIXME
        // 0440) — single-symbol describe surfaces every category incl.
        // SpecialForm. The scheme/docstring facets are pulled per-entry below.
        let category = crate::worker::classify_listing_entry(&entry)?;
        let (scheme, docstring) = match &entry {
            ModuleEntry::Def { scheme, docstring, .. } =>
                (Some(scheme.clone()), docstring.clone()),
            ModuleEntry::SpecialForm { scheme, docstring, .. } =>
                (Some(scheme.clone()), docstring.clone()),
            ModuleEntry::TraitDecl { docstring, .. } =>
                (None, docstring.clone()),
            _ => (None, None),
        };
        let source = self.shared.introspection.as_ref()
            .and_then(|m| m.get(&fq))
            .and_then(|intr| intr.source.clone());
        // FIXME 0194: populate `related` from the same cross-ref collectors the
        // universal-display paths (`format_type_display`/`format_trait_display`)
        // use, projected to `FQSymbol`s anchored at each referent's home module.
        let related = self.collect_related(&entry, &fq, &resolved_module);
        Some(SymbolDescription {
            fq,
            category,
            scheme,
            docstring,
            source,
            related,
        })
    }

    /// Collect the cross-reference `FQSymbol`s for `entry` (FIXME 0194).
    ///
    /// - **Type** (`TypeDef`, or a product ctor's type facet) → its constructor
    ///   FQs (the `; match:` arms), homed at the type's defining module.
    /// - **Trait** (`TraitDecl`) → its method-defn FQs (`; defn:`) homed at the
    ///   trait module, plus the implementing-type FQs (`; impl:`) each homed at
    ///   that type's defining module.
    /// - **Constructor** → its parent type's FQ (`; defn:`).
    ///
    /// Other kinds (plain fns, macros, special forms) have no structural
    /// cross-ref under §3.6 and return empty. Names that cannot be re-homed are
    /// skipped rather than emitted with a wrong module.
    pub(crate) fn collect_related(
        &self,
        entry: &ModuleEntry<crate::code::Code>,
        fq: &FQSymbol,
        resolved_module: &ModuleFullPath,
    ) -> Vec<FQSymbol> {
        collect_related_for(
            &self.shared.symbol_tables,
            &self.current_module_path(),
            entry,
            fq,
            resolved_module,
        )
    }

    /// §9: Format an eval result for display.
    ///
    /// Produces the universal output format (spec §1.1):
    ///   `:Type {value|name} ; {classification} - {docstring}`
    pub fn format_eval_result(&self, result: &EvalResult) -> String {
        // S83 W2 (FIXME 0363): surface accumulated typecheck `Warning`s in the
        // REPL output. Warnings are DATA accumulated through the eval chain
        // (`src/CLAUDE.md` §Error Handling: "displayed by the binary crate"),
        // but no display site existed — so a `ShadowedName` warning (e.g. a
        // synthesised §5.2.6 accessor colliding with an existing binding) was
        // invisible. Render each as a `; warning: <message>` comment line
        // (the §1.1 comment style) ahead of the value/def display. Doing it
        // here is the single source of truth: every `format_eval_result`
        // caller (REPL loop + `--run` echo + bare-symbol introspection) gets
        // warning display uniformly.
        render(&self.format_eval_result_doc(result))
    }

    /// The full eval-result `StyledDoc` — the `; warning:` lines (R6 prefix + R11
    /// detail) prepended to the value/definition body.
    fn format_eval_result_doc(&self, result: &EvalResult) -> StyledDoc {
        let body = self.format_eval_result_body_doc(result);
        if result.warnings().is_empty() {
            return body;
        }
        let mut out = StyledDoc::new();
        for w in result.warnings() {
            push_warning_line(&mut out, &w.message);
        }
        out.extend(body);
        out
    }

    /// The value/definition rendering for an `EvalResult`, without warning
    /// surfacing. `format_eval_result_doc` wraps this to prepend `; warning:`
    /// lines (FIXME 0363).
    fn format_eval_result_body_doc(&self, result: &EvalResult) -> StyledDoc {
        match result {
            EvalResult::Def { symbol, defined, .. } => {
                let name = symbol.symbol.as_ref();
                let module = &symbol.module;

                // Builtin type names (Int, Bool, etc.) from primitives module.
                if module.as_ref() == "primitives" && intrinsic_type_from_name(name).is_some() {
                    return self.format_builtin_type_display_doc(name);
                }

                let cur_module = self.current_module_path();
                // S78 §2.7.6 — prelude outer-scope hop. A bare prelude-provided
                // name (e.g. `add-i64`) is no longer flattened into the current
                // table; when the per-module fallback bit is ON, look it up in
                // prelude's own table (the `(export …)` re-export edge) so the
                // chain-follow below still reaches `primitives/add-i64`. Routes
                // through the canonical helper with `root: false` (S87 §4 dedup,
                // Principle 7) — the NO-root-tier walk is deliberate: a bare
                // special-form name must NOT resolve here (it falls through to
                // the `None` arm below); the root cleanup is deferred (§4.1).
                let (entry, lookup_module) =
                    match self.lookup_with_prelude_fallback_opt(name, false) {
                        Some((e, m)) => (Some(e), m),
                        // 0571 D2: an UNIMPORTED qualified reference (`mathx/gcount`)
                        // is not in the current scope — resolve it in its OWN
                        // module so the bare FQ display renders the `; defn`
                        // introspection envelope, IDENTICAL to the imported-bare
                        // control, instead of the generic `; defined` fallback.
                        None => match self
                            .shared
                            .symbol_tables
                            .get(module)
                            .and_then(|t| t.get(name).cloned())
                        {
                            Some(e) => (Some(e), module.clone()),
                            None => (None, cur_module.clone()),
                        },
                    };
                // Follow import chains to the definition.
                let (entry, resolved_module) = match entry {
                    Some(ref e) => self.resolve_entry_for_display(e, &lookup_module),
                    None => {
                        // TraitImpl entries have `Trait.Type` names; not in symbol table.
                        let mut doc = StyledDoc::new();
                        if let Some((trait_name, target_type)) = name.split_once('.') {
                            doc.plain("impl ");
                            push_fq_name(&mut doc, module, trait_name);
                            doc.plain(" for ");
                            push_fq_name(&mut doc, module, target_type);
                        } else {
                            push_fq_name(&mut doc, &symbol.module, symbol.symbol.as_ref());
                            doc.plain(" ");
                            push_metadata(&mut doc, "; defined");
                        }
                        return doc;
                    }
                };
                // FIXME 0542: a bare LOOKUP (`defined == false`) is pure
                // introspection — a trait's `; impl:` section is structural
                // (§4.1.4), shown even when empty. A definition ECHO
                // (`defined == true`) follows §1.1 and omits the empty section.
                let mut body =
                    self.format_def_entry_doc(&entry, name, &resolved_module, !*defined);
                // S101 (repl/spec.md §18.4): bare lookup of a broken symbol is
                // self-documenting — the ordinary per-class display (last-good
                // signature) plus the provenance comment line (R6 metadata).
                if let Some(line) = self.broken_status_line(name, &resolved_module) {
                    body.plain("\n");
                    push_metadata(&mut body, line);
                }
                body
            }
            EvalResult::Val { value, ty, .. } => {
                if ty.is_io() {
                    // Defensive path. In normal REPL flow `compile_and_execute_expr`
                    // has already run the trampoline and stripped the IO type via
                    // `unwrap_io_inline`, so this branch is unreachable for current
                    // callers. If a future caller ever constructs `EvalResult::Val`
                    // with an un-trampolined IO value, we must still honour
                    // Decision 24's consuming convention: `run_io_trampoline` is
                    // non-consuming, so `consume_io_tree` must release the outer
                    // tree afterwards. See `pipeline::unwrap_io_inline`.
                    // Drive through `cranelisp_run_io` (the reactor-driving entry
                    // under `concurrency-runtime`, byte-identical otherwise; it
                    // also consumes the tree internally) — same entry as
                    // `unwrap_io_inline` (FIXME 0457).
                    let inner_value = cranelisp_intrinsics::io::cranelisp_run_io(*value);
                    let inner_type = ty.unwrap_io().clone();
                    crate::display::result_value_doc(
                        inner_value, &inner_type, &self.shared.symbol_tables,
                    )
                } else {
                    crate::display::result_value_doc(
                        *value, ty, &self.shared.symbol_tables,
                    )
                }
            }
            // A runtime TRAP renders as the bare §18.5 line: the `runtime error: `
            // category prefix (§5.1) directly followed by the trap payload — no
            // `Error: ` prefix, no `codegen error at 0..0:` wrapper, no
            // `runtime panic: ` slot prefix (normalized away in `pipeline`).
            // §10.3: `runtime error:` is the R8 error keyword; the payload is R9.
            EvalResult::RuntimeError { message, .. } => {
                let mut doc = StyledDoc::new();
                doc.push(Role::ErrorKeyword, "runtime error:");
                doc.plain(" ");
                doc.push(Role::ErrorDetail, message.clone());
                doc
            }
        }
    }

    /// Format a definition entry with its classification (spec §1.1, §4.1).
    /// Renders the role-tagged `StyledDoc` from `format_def_entry_doc`.
    pub(crate) fn format_def_entry(
        &self,
        entry: &ModuleEntry<Code>,
        name: &str,
        module: &ModuleFullPath,
        full_trait_sections: bool,
    ) -> String {
        render(&self.format_def_entry_doc(entry, name, module, full_trait_sections))
    }

    /// Build the `:Type module/name ; classification` introspection `StyledDoc`
    /// (spec §1.1, §4.1) — R4 type annotation, R7 module prefix, R6 metadata.
    pub(crate) fn format_def_entry_doc(
        &self,
        entry: &ModuleEntry<Code>,
        name: &str,
        module: &ModuleFullPath,
        // FIXME 0542: when set, a trait entry's `; impl:` section is emitted
        // even when empty (§4.1.4 pure-introspection displays: bare lookup,
        // `/sig`, `/info`). A definition echo passes `false` (§1.1 omits the
        // empty section). Ignored for every non-trait entry.
        full_trait_sections: bool,
    ) -> StyledDoc {
        match entry {
            ModuleEntry::Def { scheme, kind, docstring, .. } => {
                match kind.as_ref() {
                    // Multi-sig: emit one line per variant per repl/spec.md
                    // §1.3 + §4.1.1.
                    DefKind::Overloaded { variants } if !variants.is_empty() => {
                        return format_overloaded_variants_doc(
                            name, module, variants, docstring.as_deref(),
                        );
                    }
                    DefKind::Constructor { type_name, type_def, .. } => {
                        let type_str = format_type_qualified(&scheme.ty);
                        let tn = TypeName::from(type_name.name.as_ref());
                        // The display authority builds the ONE canonical
                        // `module/Type.Ctor` form from the ctor's BARE name — so
                        // BOTH REPL input shapes converge here: a bare `Red` and a
                        // dotted `Color.Red` (the S109 canonical `Type.Ctor` key,
                        // which the dotted-input introspection path carries verbatim
                        // as `name`). `format_ctor_display` re-prepends `Type.`, so
                        // strip any leading `Type.` segment first or the dotted path
                        // doubles it to `Color.Color.Red` (§4.1.2/§1.5). One
                        // formatter, no per-input special-casing.
                        let bare_ctor = name.rsplit_once('.').map_or(name, |(_, c)| c);
                        // Resolve the type's `TypeDefInfo` so `format_ctor_display`
                        // can suppress the redundant `Type.Ctor` dot for a
                        // single-ctor product (`Point`, not `Point.Point`). A
                        // single-ctor product type's `name` key is THIS ctor `Def`
                        // (type-name == ctor-name; FIXME 0319), so `type_def` on
                        // `kind` is the authoritative facet — prefer it; fall back
                        // to the chain lookup for sum/enum ctors whose type is a
                        // separate `TypeDef` entry. Reaching the spurious
                        // `{type_name}.{name}` branch (e.g. `user/Point.Point`,
                        // which the outer `{module}/` then double-qualifies to
                        // `user/user/Point.Point`) is the Root-C defect (FIXME 0321).
                        let ctor_display = {
                            let info = type_def.as_deref().cloned().or_else(|| {
                                // D1 (S108, FIXME-0321 mis-qualify class): root
                                // the fallback chain-lookup at the ctor's already-
                                // RESOLVED HOME `module` (the fn param), NOT
                                // `current_module_path()`. At the home the TypeDef
                                // is local so the chain terminates at depth 0; a
                                // seeded/prelude-globbed ctor resolves its product
                                // facet instead of missing and mis-qualifying.
                                cranelisp_types::lookup_type_def_chain(
                                    &self.shared.symbol_tables, module, &tn,
                                )
                            });
                            match info {
                                Some(info) => crate::display::format_ctor_display(&tn, bare_ctor, &info),
                                None => format!("{tn}.{bare_ctor}"),
                            }
                        };
                        let mut doc = StyledDoc::new();
                        push_type_annotation(&mut doc, &type_str);
                        doc.plain(" ");
                        push_fq_name(&mut doc, module, &ctor_display);
                        doc.plain(" ");
                        push_metadata(&mut doc, "; deftype");
                        return doc;
                    }
                    DefKind::Macro { clauses_meta, .. } => {
                        return format_macro_display_doc(
                            name, clauses_meta, docstring.as_deref(), module,
                        );
                    }
                    _ => {}
                }
                // FIXME 0352 (Principle 7): both the constrained and
                // unconstrained arms render the scheme type through the single
                // `format_scheme_type` renderer (`format_scheme_display_doc` is
                // the `:type module/name` primary-line builder).
                let mut doc = crate::display::format_scheme_display_doc(name, scheme, module);
                // Both got-slotted primitives (`DefKind::Primitive`, e.g.
                // `add-i64`) and slot-less host-promised externs
                // (`DefKind::PrimitiveExtern`, e.g. the S96 `race`/`select`/
                // `sleep` builtins + `bind`/`discover-tests`/`catch-runtime-error`)
                // are `primitives`-module builtins and MUST classify as
                // `; primitive` per `repl/spec.md §1.1` — a `PrimitiveExtern`
                // dispatches by-name via `Linkage::Import` but is no less a
                // primitive to the user (FIXME 0481).
                let is_primitive = matches!(
                    kind.as_ref(),
                    DefKind::Primitive { .. } | DefKind::PrimitiveExtern
                );
                let classification = if is_primitive { "primitive" } else { "defn" };
                // FIXME 0308: primitive entries now carry their Appendix A.5
                // description on `PrimitiveDef.docstring`; read it through the
                // entry's `docstring` field directly (the parallel
                // `builtin_docs` table is retired), satisfying the §A.5 MUST +
                // the §1.1 `; primitive - <doc>` format.
                doc.plain(" ");
                push_metadata(&mut doc, classification_metadata(classification, docstring.as_deref()));
                doc
            }
            ModuleEntry::SpecialForm { scheme, description, .. } => {
                format_special_form_display_doc(name, scheme, description)
            }
            ModuleEntry::TypeDef { .. } => {
                self.format_type_display_doc(name, module)
            }
            ModuleEntry::TraitDecl { docstring, .. } => {
                // 0558 (S108, resolve-home-enumeration.md §5): pass the RESOLVED
                // HOME `module` (the fn param, produced by the gate) so the trait
                // sections root at the home — where the `TraitDecl` is local
                // (depth 0) and the prelude outer-scope question cannot arise.
                self.format_trait_display_doc(name, docstring.as_deref(), full_trait_sections, module)
            }
            _ => {
                // TraitImpl entries have `Trait.Type` symbol names and
                // aren't stored in the symbol table as named entries.
                let mut doc = StyledDoc::new();
                if let Some((trait_name, target_type)) = name.split_once('.') {
                    doc.plain("impl ");
                    push_fq_name(&mut doc, module, trait_name);
                    doc.plain(" for ");
                    push_fq_name(&mut doc, module, target_type);
                } else {
                    push_fq_name(&mut doc, module, name);
                    doc.plain(" ");
                    push_metadata(&mut doc, "; defined");
                }
                doc
            }
        }
    }

    /// Resolve Import/Reexport chains to the underlying definition entry.
    ///
    /// Walks the full chain (user → prelude → primitives → …) so that
    /// bare-value, introspection, and call paths converge on the same
    /// terminal `ModuleEntry::Def` regardless of how many re-exports sit
    /// between the current module and the defining module. Depth-limited
    /// to match the typechecker's `resolve_to_terminal_entry_owned`
    /// (spec §8.6.2 IMPORT_CHAIN_DEPTH_LIMIT). On cycle / depth exhaustion
    /// or a broken link, falls back to the last successfully resolved
    /// entry + module.
    ///
    /// Fix site for Sprint 61 Slice 1 Defect 4 (bare-primitive-name
    /// invisibility). See `design/int/bare-primitive-value-path.md`
    /// candidate 2 — the match arms in `check_bare_symbol_introspection`
    /// do not cover `Import`/`Reexport`, and the prior one-hop resolver
    /// could terminate on a `Reexport` intermediate (user → prelude →
    /// primitives), causing the bare-value path to fall through while
    /// the call and introspection paths resolved via their own recursive
    /// walks. Aligning on a single recursive resolver closes the
    /// divergence.
    pub(crate) fn resolve_entry_for_display(
        &self,
        entry: &ModuleEntry<Code>,
        current_module: &ModuleFullPath,
    ) -> (ModuleEntry<Code>, ModuleFullPath) {
        const MAX_DEPTH: usize = 32;
        let mut cur_entry = entry.clone();
        let mut cur_module = current_module.clone();
        for _ in 0..MAX_DEPTH {
            match &cur_entry {
                ModuleEntry::Import { source, .. } => {
                    match self.shared.symbol_tables.get(&source.module) {
                        Some(module_table) => {
                            match module_table.get(source.symbol.as_ref()) {
                                Some(resolved) => {
                                    let next = resolved.clone();
                                    cur_module = source.module.clone();
                                    cur_entry = next;
                                    continue;
                                }
                                None => return (cur_entry, cur_module),
                            }
                        }
                        None => return (cur_entry, cur_module),
                    }
                }
                _ => return (cur_entry, cur_module),
            }
        }
        // Depth exhausted — return the last resolved entry/module.
        (cur_entry, cur_module)
    }

    /// Format a user-defined type for display (spec §4.1.3).
    ///
    /// Shows `:module/TypeName ; deftype` with `; match:` and `; impl:` sections.
#[cfg(test)]
    pub(crate) fn format_type_display(&self, type_name: &str, module: &ModuleFullPath) -> String {
        render(&self.format_type_display_doc(type_name, module))
    }

    /// The `:module/TypeName ; deftype` type-display `StyledDoc` (spec §4.1.3) —
    /// the whole `:module/Type` is one R4 span (no `module/` decomposition inside
    /// a type annotation, §10.3 R4); `; deftype` and the `; match:`/`; impl:`
    /// drawers are R6 metadata.
    pub(crate) fn format_type_display_doc(&self, type_name: &str, module: &ModuleFullPath) -> StyledDoc {
        let mut result = StyledDoc::new();
        push_type_annotation(&mut result, &format!("{module}/{type_name}"));
        result.plain(" ");
        push_metadata(&mut result, "; deftype");
        let tn = TypeName::from(type_name);
        // FIXME 0192 method 2: `get_type_constructors` deleted; inline the
        // 1-line wrapper over the relocated `lookup_type_def_chain`.
        //
        // D1 (S108): root the constructor chain-lookup at the type's already-
        // RESOLVED HOME `module` (the fn already holds it), NOT
        // `current_module_path()`. At the home the TypeDef is local, so the
        // chain terminates at depth 0 and the implicit-prelude outer-scope hop
        // never arises — a seeded ADT (Option/Result/IO) reached via the
        // prelude glob keeps its `; match:` section (spec §4.1.3), same as a
        // user deftype (which worked only incidentally when scope == home).
        if let Some(info) = cranelisp_types::lookup_type_def_chain(
            &self.shared.symbol_tables, module, &tn,
        ) && !info.constructors.is_empty() {
            // `TypeDefInfo.constructors` is now `Vec<Symbol>` (S70 — the
            // `ConstructorInfo` struct retired; ctor metadata lives on each
            // ctor's `DefKind::Constructor` entry).
            let names: Vec<&str> = info.constructors.iter().map(|c| c.as_ref()).collect();
            result.extend(format_related_section_doc("match", &names));
        }
        // The `; impl:` view is a Decision-45 Pattern-B VIEW question ("which
        // traits does this type implement, as visible from HERE") — scope-rooted
        // by semantics. E8 (S108, resolve-home-enumeration.md §5a): the asking
        // module's view INCLUDES the prelude outer scope when its
        // `prelude_fallback` bit is ON, so the candidate SET is the UNION of the
        // inner-scope run and a prelude-hop run (the ONE `impls_for_type_in_view`
        // wrapper — never two hand-rolled hops, Principle 7).
        let trait_names = self.impls_for_type_in_view(&tn);
        if !trait_names.is_empty() {
            let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
            result.extend(format_related_section_doc("impl", &names));
        }
        result
    }

    /// Format a trait for display (spec §4.1.4).
    ///
    /// Shows `:home/TraitName ; deftrait` with `; defn:` and `; impl:` sections,
    /// ALL rooted at `home` — the trait's RESOLVED home module produced by the
    /// canonical gate (`lookup_with_prelude_fallback` → `resolve_entry_for_display`,
    /// held by the sole caller `format_def_entry`).
    ///
    /// 0558 (S108, resolve-home-enumeration.md §5, class `wrong-scope-lookup`):
    /// the prior body re-resolved the home from the asking scope
    /// (`resolve_terminal_entry_and_home`, no prelude hop) and rooted both section
    /// lookups at `scope`, so a prelude-globbed trait (reachable at `user` ONLY
    /// via the implicit outer-scope bit, no `Import` edge) dropped its `; defn:`
    /// and left `; impl:` empty. Taking the home from the gate and rooting at it —
    /// where the `TraitDecl` is LOCAL (depth 0) — makes the §4.1.4 unconditional
    /// sections survive the prelude glob. Rooting the impl enumeration at the
    /// trait's home is COMPLETE by construction: Decision 0045 writes every
    /// `impl$Type$Trait` into the trait's defining module, so "implementing types
    /// of trait T" is a home question, not a view question (Principle 17 shape 3).
    #[cfg(test)]
    pub(crate) fn format_trait_display(
        &self,
        trait_name: &str,
        docstring: Option<&str>,
        full_impl_section: bool,
        home: &ModuleFullPath,
    ) -> String {
        render(&self.format_trait_display_doc(trait_name, docstring, full_impl_section, home))
    }

    /// The `:home/TraitName ; deftrait` trait-display `StyledDoc` (spec §4.1.4) —
    /// the whole `:home/Trait` is one R4 span; the classification, docstring, and
    /// `; defn:`/`; impl:` drawers are R6 metadata.
    pub(crate) fn format_trait_display_doc(
        &self,
        trait_name: &str,
        docstring: Option<&str>,
        full_impl_section: bool,
        home: &ModuleFullPath,
    ) -> StyledDoc {
        let tn = TraitName::from(trait_name);
        let mut result = StyledDoc::new();
        push_type_annotation(&mut result, &format!("{home}/{trait_name}"));
        result.plain(" ");
        push_metadata(&mut result, append_docstring_comment("; deftrait".to_string(), docstring));
        // FIXME 0542 (§4.1.4): a bare trait lookup MUST ALWAYS surface BOTH the
        // `; defn:` (method names) and `; impl:` (implementing types) sections —
        // for user-module traits and stdlib traits alike, and even when the
        // trait has no impls yet (the `; impl:` header appears with an empty
        // body). This is DELIBERATELY UNCONDITIONAL, unlike the type-display
        // rule (§4.1.3), where an empty `; impl:` section is omitted: a trait's
        // related sections are structural, a type's are conditional.
        // FIXME 0192 method 4: `get_trait_methods` deleted; inline the 1-line
        // wrapper over `lookup_trait_decl_chain` — rooted at the trait's HOME.
        let method_names: Vec<String> = cranelisp_types::lookup_trait_decl_chain(
            &self.shared.symbol_tables, home, &tn,
        )
        .map(|decl| decl.methods.iter().map(|m| m.name.to_string()).collect())
        .unwrap_or_default();
        let impl_type_names: Vec<String> = cranelisp_types::get_implementing_types_chain(
            &self.shared.symbol_tables, home, &tn,
        )
        .iter()
        .map(|t| t.to_string())
        .collect();
        let method_refs: Vec<&str> = method_names.iter().map(String::as_str).collect();
        let impl_refs: Vec<&str> = impl_type_names.iter().map(String::as_str).collect();
        result.extend(format_trait_related_sections_doc(
            &method_refs,
            &impl_refs,
            full_impl_section,
        ));
        result
    }

    /// Format a builtin type (Int, Bool, Float, String) for display (spec §4.1.3).
    pub(crate) fn format_builtin_type_display(&self, type_name: &str) -> String {
        render(&self.format_builtin_type_display_doc(type_name))
    }

    /// The `:primitives/TypeName ; type` builtin-type `StyledDoc` (spec §4.1.3).
    pub(crate) fn format_builtin_type_display_doc(&self, type_name: &str) -> StyledDoc {
        let tn = TypeName::from(type_name);
        let mut result = StyledDoc::new();
        push_type_annotation(&mut result, &format!("primitives/{type_name}"));
        result.plain(" ");
        push_metadata(&mut result, "; type");
        // E8 (S108, resolve-home-enumeration.md §5a): the same ONE view wrapper
        // that feeds `format_type_display` — the candidate SET is the inner-scope
        // run ∪ the prelude hop (bit-gated), so a bare `Int` under the prelude
        // surfaces its prelude-globbed trait impls (`; impl: Display Eq Num Ord`,
        // §4.1.3). Sharing the wrapper closes the two-formatter sibling gap that
        // recurs when one is fixed and the other is not (the Inc1 D1/D2 lesson).
        let trait_names = self.impls_for_type_in_view(&tn);
        if !trait_names.is_empty() {
            let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
            result.extend(format_related_section_doc("impl", &names));
        }
        result
    }

    /// The type-side `; impl:` VIEW's candidate-trait enumeration (E8, S108,
    /// resolve-home-enumeration.md §5a). "Which traits does this type implement,
    /// as visible from the current scope" is a Decision-45 Pattern-B VIEW
    /// question — scope-rooted by semantics. But "scope-rooted" governs the
    /// per-candidate ROOTING and the answer's frame, NOT the candidate SET: the
    /// asking module's view INCLUDES the prelude outer scope whenever its
    /// `prelude_fallback` bit is ON (S78 §2 — that is what the bit means), so the
    /// candidate enumeration is the UNION of:
    ///
    /// - the inner-scope run — `get_impls_for_type_chain(tables, scope, tn)`; and
    /// - the prelude-hop run — the SAME reader rooted at `prelude`, when the bit
    ///   is ON and scope ≠ `prelude`, restricted to prelude heads that pass the
    ///   I-1 public-only filter (a PRIVATE prelude trait must NOT leak into a user
    ///   view — the `recognize_macro_head` / `prelude_terminal_visible`
    ///   discipline). Since `cranelisp-types` takes no visibility parameter and
    ///   does not change, the filter is an int-side POST-filter on the head entry.
    ///
    /// Merged by bare `TraitName`, sorted + deduped (name-dedup is safe: a
    /// scope-local trait and a distinct prelude trait sharing a bare name is a
    /// poisoned name upstream per §8.6.5, so the union cannot conflate two live
    /// traits). Per-candidate home-probing is unchanged (Decision 0045 makes the
    /// per-trait answer complete by construction). This is the ONE session wrapper
    /// feeding BOTH `format_type_display` and `format_builtin_type_display`
    /// (Principle 7 — never two hand-rolled hops).
    fn impls_for_type_in_view(&self, tn: &TypeName) -> Vec<TraitName> {
        let scope = self.current_module_path();
        let mut traits = cranelisp_types::get_impls_for_type_chain(
            &self.shared.symbol_tables, &scope, tn,
        );
        let prelude_path = ModuleFullPath::from("prelude");
        if scope != prelude_path {
            let bit_on = self
                .shared
                .prelude_fallback
                .get(&scope)
                .map(|b| *b)
                .unwrap_or(false);
            if bit_on {
                for t in cranelisp_types::get_impls_for_type_chain(
                    &self.shared.symbol_tables, &prelude_path, tn,
                ) {
                    // I-1 public-head post-filter: drop a prelude-run trait whose
                    // head entry in prelude's OWN table is not public.
                    if self.prelude_trait_head_is_public(&t) {
                        traits.push(t);
                    }
                }
            }
        }
        traits.sort();
        traits.dedup();
        traits
    }

    /// I-1 public-head filter for the E8 prelude hop: `true` iff trait `t`'s head
    /// entry in prelude's OWN table is public. A private prelude trait
    /// (`deftrait-`) must not leak into a user's type-side `; impl:` view. Mirrors
    /// `recognize_macro_head`'s prelude-retry post-filter + typecheck's
    /// `prelude_terminal_visible`.
    fn prelude_trait_head_is_public(&self, t: &TraitName) -> bool {
        let prelude_path = ModuleFullPath::from("prelude");
        self.shared
            .symbol_tables
            .get(&prelude_path)
            .and_then(|tbl| tbl.get(t.as_ref()).map(|e| e.is_public()))
            .unwrap_or(false)
    }
}


#[cfg(test)]
mod collect_related_tests {
    use super::*;
    
    

    
    use cranelisp_types::{
        FQTypeName, ModuleFullPath, Scheme, TypeDefInfo, TypeName, Visibility,
    };
    use std::collections::HashMap;

    fn tables() -> dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
        dashmap::DashMap::new()
    }

    fn ensure(tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>, path: &str) {
        let p = ModuleFullPath::from(path);
        tables
            .entry(p.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(p));
    }

    fn fq(module: &str, symbol: &str) -> FQSymbol {
        FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(symbol),
        }
    }

    // spec: repl/spec.md §3.6 — `SymbolDescription.related` (FIXME 0194). A TYPE
    // symbol's related set is its constructors, homed at the type's defining
    // module. Before SW-C `related` was stubbed empty; this pins the population.
    #[test]
    fn related_populated_for_type_lists_its_constructors() {
        let tables = tables();
        ensure(&tables, "user");
        let user = ModuleFullPath::from("user");

        // (deftype Color [Red Green]) — a sum type with two nullary ctors.
        let type_entry = ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: FQTypeName::new(user.clone(), TypeName::from("Color")),
                type_params: vec![],
                constructors: vec![Symbol::from("Red"), Symbol::from("Green")],
            },
            visibility: Visibility::Public,
            docstring: None,
        };

        let related = collect_related_for(&tables, &user, &type_entry, &fq("user", "Color"), &user);

        assert!(
            related.contains(&fq("user", "Red")) && related.contains(&fq("user", "Green")),
            "a type's `related` MUST list its constructors homed at the type's \
             module (spec §3.6); got {related:?}",
        );
        assert!(
            !related.is_empty(),
            "`related` MUST NOT be the empty stub it was before FIXME 0194",
        );
    }

    // spec: repl/spec.md §3.6 — a CONSTRUCTOR's related set names its parent
    // type, homed at the type's defining module.
    #[test]
    fn related_populated_for_constructor_names_its_type() {
        let tables = tables();
        ensure(&tables, "user");
        let user = ModuleFullPath::from("user");

        let ctor_entry = ModuleEntry::def(
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::ADT(
                    FQTypeName::new(user.clone(), TypeName::from("Color")),
                    vec![],
                ),
            },
            DefKind::Constructor {
                got_slot: 0,
                type_name: FQTypeName::new(user.clone(), TypeName::from("Color")),
                type_def: None,
                tag: 0,
                field_count: 0,
                internal: false,
                mode_summary: None,
            },
        )
        .visibility(Visibility::Public)
        .build();

        let related = collect_related_for(&tables, &user, &ctor_entry, &fq("user", "Red"), &user);

        assert!(
            related.contains(&fq("user", "Color")),
            "a constructor's `related` MUST name its parent type (spec §3.6); \
             got {related:?}",
        );
    }
}

// ---------------------------------------------------------------------------
// Sprint 58 Wave 4 Step 5d (ii): multi-sig REPL bare-symbol display.
// spec: repl/spec.md §1.3 + §4.1.1 — overloaded fn shows all variant
// signatures, one per line.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod overloaded_display_tests {
    use super::*;
    
    

    

    fn variant(params: Vec<Type>, ret: Type, mangled: &str) -> OverloadVariant {
        OverloadVariant {
            param_types: params,
            ret_type: ret,
            mangled_name: Symbol::from(mangled),
        }
    }

    // spec: repl/spec.md §1.3 + §4.1.1 — multi-sig display emits ≥2 lines.
    #[test]
    fn overloaded_display_emits_one_line_per_variant() {
        let module = ModuleFullPath::from("user");
        let variants = vec![
            variant(vec![Type::Int], Type::Int, "pick$Int"),
            variant(vec![Type::Int, Type::Int], Type::Int, "pick$Int+Int"),
        ];
        let out = format_overloaded_variants("pick", &module, &variants, None);
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(
            lines.len(),
            2,
            "two variants must produce two lines, got: {out}"
        );
        // Both lines mention the qualified name.
        for line in &lines {
            assert!(
                line.contains("user/pick"),
                "each variant line must include qualified name, got: {line}"
            );
        }
        // First variant's parameter shape: `[primitives/Int]`.
        assert!(
            lines[0].contains("[primitives/Int]"),
            "first line must show 1-arg signature, got: {}",
            lines[0]
        );
        // Second variant's parameter shape: `[primitives/Int primitives/Int]`.
        assert!(
            lines[1].contains("[primitives/Int primitives/Int]"),
            "second line must show 2-arg signature, got: {}",
            lines[1]
        );
        // Only the first line carries the `; defn` classification.
        assert!(
            lines[0].contains("; defn"),
            "first line must carry `; defn` classification, got: {}",
            lines[0]
        );
        assert!(
            !lines[1].contains("; defn"),
            "second line MUST NOT repeat `; defn` classification, got: {}",
            lines[1]
        );
    }

    // spec: repl/spec.md §4.1.1 — first variant carries the docstring; later
    // variants do not.
    #[test]
    fn overloaded_display_attaches_docstring_to_first_variant_only() {
        let module = ModuleFullPath::from("user");
        let variants = vec![
            variant(vec![Type::Int], Type::Int, "pick$Int"),
            variant(vec![Type::Int, Type::Int], Type::Int, "pick$Int+Int"),
        ];
        let out = format_overloaded_variants(
            "pick", &module, &variants, Some("Pick one or sum two"),
        );
        let lines: Vec<&str> = out.lines().collect();
        assert!(
            lines[0].contains("Pick one or sum two"),
            "first line must include the docstring, got: {}",
            lines[0]
        );
        assert!(
            !lines[1].contains("Pick one or sum two"),
            "second line MUST NOT repeat the docstring, got: {}",
            lines[1]
        );
    }

    // spec: repl/spec.md §4.1.1 — single-variant degenerate case is correct
    // (one line, no duplication).
    #[test]
    fn overloaded_display_single_variant_emits_one_line() {
        let module = ModuleFullPath::from("user");
        let variants = vec![variant(vec![Type::Int], Type::Int, "id$Int")];
        let out = format_overloaded_variants("id", &module, &variants, None);
        assert_eq!(
            out.lines().count(),
            1,
            "single-variant Overloaded must emit one line, got: {out}"
        );
    }

}

// ---------------------------------------------------------------------------
// FIXME 0542 — bare trait lookup always surfaces `; defn:` and `; impl:`
// sections. Unit-tests the extracted always-emit section builder
// (`format_trait_related_sections`) at the exact seam of the fix.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod trait_related_section_tests {
    use super::*;
    
    

    

    // spec: repl/spec.md §4.1.4 — a PURE INTROSPECTION display
    // (`full_impl_section = true`: bare lookup / `/sig` / `/info`) surfaces the
    // `; impl:` section even when the trait has NO implementing types yet (the
    // header with an empty body). This is the FIXME-0542 seam.
    #[test]
    fn trait_sections_full_emits_impl_header_when_impls_empty() {
        let out = format_trait_related_sections(&["show"], &[], true);
        assert!(
            out.contains("; defn:") && out.contains("show"),
            "the `; defn:` method section MUST list `show`; got:\n{out}",
        );
        assert!(
            out.contains("; impl:"),
            "a full introspection display MUST surface the `; impl:` section \
             even with no impls (§4.1.4, FIXME 0542); got:\n{out}",
        );
    }

    // spec: repl/spec.md §1.1 — a DEFINITION ECHO (`full_impl_section = false`)
    // of a freshly-defined impl-less trait OMITS the empty `; impl:` section
    // (matching the §1.1 example) so introspection lists exactly one `; impl:`
    // section for the trait. Regression guard for the negative /qa parser.
    #[test]
    fn trait_sections_echo_omits_empty_impl_header() {
        let out = format_trait_related_sections(&["show"], &[], false);
        assert!(
            out.contains("; defn:") && out.contains("show"),
            "the `; defn:` section MUST still appear on a definition echo; \
             got:\n{out}",
        );
        assert!(
            !out.contains("; impl:"),
            "a definition echo MUST omit the empty `; impl:` section (§1.1); \
             got:\n{out}",
        );
    }

    // spec: repl/spec.md §4.1.4 — when impls exist the `; impl:` section lists
    // the implementing types and NOTHING else (positive + negative in one).
    // With impls present the section appears regardless of the flag.
    #[test]
    fn trait_sections_impl_lists_only_implementing_types() {
        for full in [true, false] {
            let out = format_trait_related_sections(&["show"], &["Int"], full);
            // Isolate the `; impl:` body rows (comment lines after the header).
            let impl_body: Vec<&str> = out
                .lines()
                .skip_while(|l| l.trim() != "; impl:")
                .skip(1)
                .take_while(|l| l.trim_start().starts_with(';'))
                .collect();
            let joined = impl_body.join(" ");
            assert!(
                joined.contains("Int"),
                "the `; impl:` section MUST list `Int` (full={full}); \
                 body={impl_body:?}",
            );
            assert!(
                !joined.contains("Bool"),
                "the `; impl:` section MUST NOT leak an unrelated type `Bool` \
                 (full={full}); body={impl_body:?}",
            );
        }
    }
}

// ---------------------------------------------------------------------------
// FIXME 0546 — `/imports` "Prelude (implicit)" group renders through the shared
// §3.3 L0–L4 layout (not one name per line), preserving the header suffix
// comment. Unit-tests the extracted `format_prelude_implicit_group` at the fix
// seam + confirms `append_name_category` shares the same layout body.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod prelude_group_layout_tests {
    use super::*;
    
    

    

    // A 12-name set (2 operators + 10 letter-grouped names) that the shared
    // layout MUST pack multi-column (≤6/line), not one-per-line.
    fn names() -> Vec<String> {
        [
            "+", "-", "abs", "add", "ceil", "cons", "drop", "each", "map",
            "nth", "when", "zip",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect()
    }

    // spec: repl/spec.md §3.4 — the "Prelude (implicit)" header suffix comment
    // is preserved verbatim by the shared-layout routing (FIXME 0546).
    #[test]
    fn prelude_group_preserves_header_suffix_comment() {
        let out = format_prelude_implicit_group(&names());
        let header = out.lines().next().unwrap_or("");
        assert!(
            header.starts_with("Prelude (implicit):")
                && header.contains("available via the prelude outer scope"),
            "the header suffix comment MUST be preserved; header={header:?}",
        );
        // The suffix MUST describe the §8.6.4 CONFLICT semantics, NOT "shadowing":
        // a def (or a clashing import) of a prelude name is a compile-time error
        // resolved by the fully-qualified name — never a silent override.
        assert!(
            header.contains("conflicts") && header.contains("fully-qualified"),
            "suffix MUST describe the §8.6.4 conflict + FQ resolution; header={header:?}",
        );
        assert!(
            !header.contains("shadow"),
            "prelude names are NOT shadowed by a def/import of the same name — \
             that is a §8.6.4 conflict; header={header:?}",
        );
    }

    // spec: repl/spec.md §3.3/§3.4 — the prelude names render through the SHARED
    // multi-column layout: some body row packs ≥2 names, none exceeds 6, and the
    // body is byte-identical to `format_symbol_layout` for the same name set —
    // NOT one name per line (FIXME 0546).
    #[test]
    fn prelude_group_body_uses_shared_layout() {
        let ns = names();
        let out = format_prelude_implicit_group(&ns);
        let body: Vec<&str> = out
            .lines()
            .skip(1) // header
            .map(|l| l.strip_prefix("  ").unwrap_or(l))
            .collect();
        assert!(
            body.iter().any(|l| l.split_whitespace().count() >= 2),
            "the prelude group MUST use the shared multi-column layout, not \
             one name per line; body={body:?}",
        );
        for row in &body {
            assert!(
                row.split_whitespace().count() <= 6,
                "a shared-layout row holds at most 6 names; row={row:?}",
            );
        }
        // Byte-identical to the shared formatter for this name set.
        let expected = format_symbol_layout(&ns);
        assert_eq!(
            body, expected,
            "the prelude group body MUST equal `format_symbol_layout` output \
             (single-sourced §3.3 layout)",
        );
    }

    // The prelude group and `append_name_category` share ONE layout body
    // (Principle 7) — the same names produce the same rows through both.
    #[test]
    fn prelude_group_and_category_share_layout_body() {
        let ns = names();
        let prelude = format_prelude_implicit_group(&ns);
        let prelude_body: Vec<&str> = prelude
            .lines()
            .skip(1)
            .map(|l| l.strip_prefix("  ").unwrap_or(l))
            .collect();

        let mut cat = String::new();
        append_name_category(&mut cat, "Fns", &ns);
        let cat_body: Vec<&str> = cat
            .lines()
            .skip(1) // "Fns:" header
            .map(|l| l.strip_prefix("  ").unwrap_or(l))
            .collect();

        assert_eq!(
            prelude_body, cat_body,
            "the prelude group and a normal category MUST share the layout body",
        );
    }
}

#[cfg(test)]
mod fq_arg_format_tests {
    use super::*;
    
    
    use crate::repl::test_support::*;
    
    use cranelisp_types::{
        ModuleEntry, ModuleFullPath, Span,
        Symbol, Visibility,
    };
    

    // spec: repl/spec.md §4.1.2/§1.5 (0570-sibling display-envelope-mirror) — the
    // constructor display authority renders the ONE canonical `user/Color.Red`
    // for BOTH the bare-input `name = "Red"` and the dotted-input `name =
    // "Color.Red"` (the S109 canonical key), never doubling the type segment to
    // `user/Color.Color.Red`. Byte-equality of the two input shapes at the single
    // `format_def_entry` seam guards the convergence (one formatter, no per-input
    // special-case).
    #[test]
    fn constructor_display_bare_and_dotted_input_render_one_canonical_home() {
        let s = session();
        let ctor = install_color_red(&s);
        let user = s.current_module_path();
        let bare = s.format_def_entry(&ctor, "Red", &user, true);
        let dotted = s.format_def_entry(&ctor, "Color.Red", &user, true);
        assert_eq!(
            bare, dotted,
            "bare `Red` and dotted `Color.Red` MUST render the identical §4.1.2 \
             constructor line; got bare={bare:?} dotted={dotted:?}"
        );
        assert!(
            dotted.contains("user/Color.Red") && !dotted.contains("Color.Color.Red"),
            "the dotted input MUST render the single canonical `user/Color.Red`, \
             never the doubled `user/Color.Color.Red`; got: {dotted}"
        );
    }
    // §18.5 (trap presentation): an `EvalResult::RuntimeError` renders as the
    // bare `runtime error: {payload}` line — the §5.1 category prefix directly
    // followed by the trap message, with NONE of the wrapper chain the pre-fix
    // path emitted (`Error: codegen error at 0..0: runtime error: runtime
    // panic: …`). spec: repl/spec.md §18.5
    #[test]
    fn runtime_error_renders_bare_normative_format() {
        let s = session();
        let payload = "user/g is broken by the redefinition of user/f: \
                       type error at 24..34: type mismatch: expected \
                       primitives/String, got primitives/Int";
        let out = s.format_eval_result(&super::EvalResult::RuntimeError {
            message: payload.to_string(),
            warnings: Vec::new(),
        });
        assert_eq!(out, format!("runtime error: {payload}"));
        assert!(!out.contains("Error:"), "no Error: prefix; got: {out}");
        assert!(!out.contains("codegen error"), "no codegen wrapper; got: {out}");
        assert!(!out.contains("runtime panic:"), "no slot prefix; got: {out}");
        assert!(!out.contains("0..0"), "no synthetic span; got: {out}");
    }
    // D1 (S108): `format_type_display` for a type whose resolved home is NOT
    // the current REPL module surfaces its constructors under `; match:`. The
    // bootstrapped `Option` lives in `primitives`; the current module is
    // `user`. Rooting the constructor chain-lookup at the RESOLVED HOME
    // `module` (the param) — not `current_module_path()` (`user`) — makes the
    // TypeDef local so the chain terminates at depth 0 and the seeded ADT keeps
    // its `; match:` section. spec: repl/spec.md §4.1.3
    #[test]
    fn format_type_display_roots_match_section_at_resolved_home() {
        let s = session();
        let prim = ModuleFullPath::from("primitives");
        // Sanity: the current module is NOT the type's home, so the pre-fix
        // scope-rooted lookup (from `user`) would have missed the ctors.
        assert_ne!(s.current_module_path(), prim);
        let out = s.format_type_display("Option", &prim);
        assert!(
            out.contains(":primitives/Option ; deftype"),
            "primary line must qualify the home; got: {out}"
        );
        assert!(
            out.contains("; match:"),
            "seeded ADT resolved from a non-current home MUST surface `; match:`; got: {out}"
        );
        assert!(
            out.contains("None") && out.contains("Some"),
            "`; match:` MUST list ctors None and Some; got: {out}"
        );
    }
    // 0558 (resolve-home-enumeration.md §5): `format_trait_display` roots its
    // `; defn:`/`; impl:` sections at the RESOLVED HOME passed by the gate — where
    // the `TraitDecl` is local (depth 0) — not the asking scope. A trait `T`
    // defined in `home` (not the current `user` scope) surfaces `:home/T` plus its
    // method and impl sections; the pre-fix scope-rooted lookup mis-homed to
    // `:user/T` and dropped both sections. spec: repl/spec.md §4.1.4
    #[test]
    fn format_trait_display_roots_sections_at_resolved_home() {
        use cranelisp_types::{TraitDeclInfo, TraitMethodSig, TraitName, TypeExpr};
        let s = session();
        let home = ModuleFullPath::from("home");
        let mut table = SessionSymbolTable::new_with_params(home.clone());
        table.insert(
            Symbol::from("T"),
            ModuleEntry::TraitDecl {
                info: TraitDeclInfo {
                    name: TraitName::from("T"),
                    type_params: vec![],
                    methods: vec![TraitMethodSig {
                        name: Symbol::from("mm"),
                        docstring: None,
                        params: vec![],
                        ret_type: TypeExpr::SelfType,
                        span: Span::SYNTHETIC,
                        hkt_param_index: None,
                        default_body: None,
                    }],
                },
                visibility: Visibility::Public,
                docstring: None,
            },
        );
        table.insert(Symbol::from("T.Widget"), impl_entry(&home, "T", "Widget"));
        s.shared.symbol_tables.insert(home.clone(), table);

        // The current scope is `user`, where `T` is NOT reachable — a scope-rooted
        // lookup (the pre-fix bug) would mis-home to `:user/T` + empty sections.
        assert_ne!(s.current_module_path(), home);
        let out = s.format_trait_display("T", None, true, &home);
        assert!(
            out.contains(":home/T ; deftrait"),
            "primary line MUST qualify the RESOLVED home, not the asking scope; got: {out}"
        );
        assert!(!out.contains(":user/T"), "must NOT mis-home to the asking scope; got: {out}");
        assert!(
            out.contains("; defn:") && out.contains("mm"),
            "the `; defn:` section MUST list method `mm` (home-rooted); got: {out}"
        );
        assert!(
            out.contains("; impl:") && out.contains("Widget"),
            "the `; impl:` section MUST list `Widget` (home-rooted); got: {out}"
        );
    }
    // E8 (resolve-home-enumeration.md §5a): the type-side `; impl:` VIEW's
    // candidate SET unions the inner-scope run with a PRELUDE-HOP run when the
    // asking scope's `prelude_fallback` bit is ON — so a PUBLIC prelude-globbed
    // trait's impl on the type surfaces. spec: repl/spec.md §4.1.3
    #[test]
    fn impls_for_type_in_view_unions_public_prelude_trait() {
        use cranelisp_types::TypeName;
        let s = session();
        let prelude = ModuleFullPath::from("prelude");
        let scope = s.current_module_path();
        let mut ptbl = SessionSymbolTable::new_with_params(prelude.clone());
        ptbl.insert(Symbol::from("Disp"), trait_decl_entry("Disp", Visibility::Public));
        ptbl.insert(Symbol::from("Disp.Int"), impl_entry(&prelude, "Disp", "Int"));
        s.shared.symbol_tables.insert(prelude.clone(), ptbl);
        s.shared.prelude_fallback.insert(scope, true);

        let traits = s.impls_for_type_in_view(&TypeName::from("Int"));
        assert!(
            traits.iter().any(|t| t.as_ref() == "Disp"),
            "the type-side `; impl:` view MUST include the prelude-globbed trait via \
             the prelude hop; got: {traits:?}"
        );
    }
    // E8 negative: a SUPPRESSED prelude (the `prelude_fallback` bit OFF, e.g.
    // `(import [prelude []])`) yields NO prelude-trait rows in the view.
    // spec: repl/spec.md §4.1.3
    #[test]
    fn impls_for_type_in_view_suppressed_prelude_shows_no_prelude_rows() {
        use cranelisp_types::TypeName;
        let s = session();
        let prelude = ModuleFullPath::from("prelude");
        let mut ptbl = SessionSymbolTable::new_with_params(prelude.clone());
        ptbl.insert(Symbol::from("Disp"), trait_decl_entry("Disp", Visibility::Public));
        ptbl.insert(Symbol::from("Disp.Int"), impl_entry(&prelude, "Disp", "Int"));
        s.shared.symbol_tables.insert(prelude.clone(), ptbl);
        // Bit deliberately NOT set (absence-is-OFF) — the suppressed-prelude case.

        let traits = s.impls_for_type_in_view(&TypeName::from("Int"));
        assert!(
            !traits.iter().any(|t| t.as_ref() == "Disp"),
            "with the prelude bit OFF, NO prelude-trait rows appear; got: {traits:?}"
        );
    }
    // E8 negative: a PRIVATE prelude trait (`deftrait-`) MUST NOT leak into a
    // user's type-side view — the I-1 public-head post-filter drops it.
    // spec: repl/spec.md §4.1.3
    #[test]
    fn impls_for_type_in_view_drops_private_prelude_trait() {
        use cranelisp_types::TypeName;
        let s = session();
        let prelude = ModuleFullPath::from("prelude");
        let scope = s.current_module_path();
        let mut ptbl = SessionSymbolTable::new_with_params(prelude.clone());
        ptbl.insert(Symbol::from("Secret"), trait_decl_entry("Secret", Visibility::Private));
        ptbl.insert(Symbol::from("Secret.Int"), impl_entry(&prelude, "Secret", "Int"));
        s.shared.symbol_tables.insert(prelude.clone(), ptbl);
        s.shared.prelude_fallback.insert(scope, true);

        let traits = s.impls_for_type_in_view(&TypeName::from("Int"));
        assert!(
            !traits.iter().any(|t| t.as_ref() == "Secret"),
            "a PRIVATE prelude trait MUST NOT leak into a user's `; impl:` view; got: {traits:?}"
        );
    }
    // E8 positive (scope-local): a trait + impl in the CURRENT scope surfaces via
    // the inner-scope run alone (no prelude hop needed) — the union preserves the
    // Pattern-B inner-scope answer. spec: repl/spec.md §4.1.3
    #[test]
    fn impls_for_type_in_view_includes_scope_local_trait() {
        use cranelisp_types::TypeName;
        let s = session();
        let scope = s.current_module_path();
        if let Some(mut tbl) = s.shared.symbol_tables.get_mut(&scope) {
            tbl.insert(Symbol::from("Loc"), trait_decl_entry("Loc", Visibility::Public));
            tbl.insert(Symbol::from("Loc.Gadget"), impl_entry(&scope, "Loc", "Gadget"));
        } else {
            let mut tbl = SessionSymbolTable::new_with_params(scope.clone());
            tbl.insert(Symbol::from("Loc"), trait_decl_entry("Loc", Visibility::Public));
            tbl.insert(Symbol::from("Loc.Gadget"), impl_entry(&scope, "Loc", "Gadget"));
            s.shared.symbol_tables.insert(scope.clone(), tbl);
        }

        let traits = s.impls_for_type_in_view(&TypeName::from("Gadget"));
        assert!(
            traits.iter().any(|t| t.as_ref() == "Loc"),
            "a scope-local trait's impl MUST surface via the inner-scope run; got: {traits:?}"
        );
    }
    // E8 negative (§4.1.3 empty-omitted unchanged): with no impls reachable, the
    // type display omits the `; impl:` section entirely (the type rule, unlike a
    // trait's unconditional sections). spec: repl/spec.md §4.1.3
    #[test]
    fn builtin_type_display_omits_empty_impl_section() {
        let s = session();
        // No prelude bit, no trait impls → the view is empty → no `; impl:`.
        let out = s.format_builtin_type_display("Int");
        assert!(
            out.contains(":primitives/Int ; type"),
            "the primary type line is present; got: {out}"
        );
        assert!(
            !out.contains("; impl:"),
            "an empty `; impl:` section MUST be omitted for a type (§4.1.3); got: {out}"
        );
    }
}

#[cfg(test)]
mod styling_colour_on_tests {
    use super::*;
    
    
    use crate::style::test_support::ColorGuard;

    // K3 — the introspection primary line's metadata suffix `; classification -
    // docstring` is one R6 dim span (§10.3 R6). Composed exactly as
    // `format_def_entry_doc`'s fn arm does: scheme primary line + ` ` +
    // classification metadata.
    // spec: repl/spec.md §10.3 R4/R7/R6 — `/sig` / bare-symbol introspection line.
    #[test]
    fn colour_on_k3_defn_line_metadata_dim() {
        let _g = ColorGuard::force(true);
        let scheme = Scheme {
            type_vars: Vec::new(),
            constraints: std::collections::HashMap::new(),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
        };
        let module = ModuleFullPath::from("user");
        let mut doc = crate::display::format_scheme_display_doc("double", &scheme, &module);
        doc.plain(" ");
        push_metadata(&mut doc, classification_metadata("defn", Some("Multiply by 2")));
        assert_eq!(
            render(&doc),
            "\x1b[36m:(Fn [primitives/Int] primitives/Int)\x1b[0m \x1b[2muser/\x1b[0mdouble \
             \x1b[2m; defn - Multiply by 2\x1b[0m"
        );
    }
    // K4 — a `; match:` (or `; defn:`/`; impl:`) drawer: BOTH the header AND the
    // name-body rows are R6 dim (§10.3 R6); the `\n` line breaks stay Plain.
    // spec: repl/spec.md §10.3 R6 — introspection drawers.
    #[test]
    fn colour_on_k4_drawer_header_and_body_dim() {
        let _g = ColorGuard::force(true);
        let out = render(&format_related_section_doc("match", &["Red", "Green", "Blue"]));
        // The name-body layout sorts alphabetically (§3.3); the roles are what
        // this fixture pins — the whole header AND body rows are R6 dim.
        assert_eq!(
            out,
            "\n\x1b[2m; match:\x1b[0m\n\x1b[2m;  Blue Green Red\x1b[0m"
        );
    }
    // K9 — a `; warning:` line: the `; warning: ` prefix is R6 dim metadata, the
    // message body R11 yellow warn-detail (§10.3 K9 composition). Fail-on-revert
    // pin for the `push_warning_line` role composition (the only colour-off e2e
    // existed pre-Wave-D2).
    // spec: repl/spec.md §10.3 R6/R11 — `; warning:` line.
    #[test]
    fn colour_on_k9_warning_line_r6_r11() {
        let _g = ColorGuard::force(true);
        let mut doc = StyledDoc::new();
        push_warning_line(&mut doc, "shadowed name x");
        assert_eq!(
            render(&doc),
            "\x1b[2m; warning: \x1b[0m\x1b[33mshadowed name x\x1b[0m\n"
        );
        // Colour-OFF byte-identical to the plain `; warning: <msg>` line.
        drop(_g);
        let _off = ColorGuard::force(false);
        let mut plain = StyledDoc::new();
        push_warning_line(&mut plain, "shadowed name x");
        assert_eq!(render(&plain), "; warning: shadowed name x\n");
    }
    // K11 — a `/list` category header is R12 bold; the name bodies stay default
    // (R15) layout (the scope boundary, §10.3). Pins the header role only.
    // spec: repl/spec.md §10.3 R12 — category header.
    #[test]
    fn colour_on_k11_category_header_bold() {
        let _g = ColorGuard::force(true);
        let mut buf = String::new();
        append_name_category(&mut buf, "Fns", &["double".to_string(), "area".to_string()]);
        assert!(
            buf.starts_with("\x1b[1mFns:\x1b[0m\n"),
            "category header must be R12 bold: {buf:?}"
        );
        // The name bodies carry no SGR (default-styled layout, out of scope).
        assert!(!buf["\x1b[1mFns:\x1b[0m\n".len()..].contains('\u{1b}'), "body plain: {buf:?}");
    }
}
