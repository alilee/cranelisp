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

/// Resolve a trait or type NAME to its **canonical home module** for the
/// impl-confirmation line (FIXME 0671; `resolve-home-enumeration.md` §3 rule-1).
///
/// The impl line `impl <trait> for <type>` must qualify each name by the module
/// where it actually LIVES, not the asking module the impl record sits in
/// (`Display`'s home is `text.display`, `Int`'s is `primitives` — never `user`).
/// Chain-follows the name from `scope` to its terminal home once (P24 "resolve
/// once", P26 read the settled home); consults the prelude fallback for a
/// prelude-provided name (`Display`/`Int`) not directly in scope; falls back to
/// `fallback` only when the name is genuinely unresolvable (no worse than the old
/// asking-module stamp).
pub(crate) fn impl_line_home_for(
    tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    prelude_fallback: &cranelisp_typecheck::PreludeFallback,
    scope: &ModuleFullPath,
    name: &str,
    fallback: &ModuleFullPath,
) -> ModuleFullPath {
    // Direct chain-follow from the asking scope to the terminal home.
    if let Some((_, home)) = cranelisp_types::resolve_terminal_entry_and_home(tables, scope, name) {
        return home;
    }
    // Prelude outer-scope hop: a prelude-provided name (Display, Int) not in the
    // scope's own table resolves through prelude's table when the fallback bit is
    // ON. Public-head filtered (I-1) — a private prelude head is not in scope.
    let prelude = ModuleFullPath::from("prelude");
    if scope != &prelude && prelude_fallback.get(scope).map(|b| *b).unwrap_or(false) {
        let head_public = tables
            .get(&prelude)
            .and_then(|t| t.get(name).map(|e| e.is_public()))
            .unwrap_or(false);
        if head_public
            && let Some((_, home)) =
                cranelisp_types::resolve_terminal_entry_and_home(tables, &prelude, name)
        {
            return home;
        }
    }
    fallback.clone()
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
pub(crate) fn classification_metadata(classification: &str, docstring: Option<&str>) -> String {
    append_docstring_comment(format!("; {classification}"), docstring)
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
        cranelisp_types::resolve_terminal_entry_and_home(tables, scope, name).map(|(_, home)| {
            FQSymbol {
                module: home,
                symbol: Symbol::from(name),
            }
        })
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
            if let DefKind::Constructor {
                type_name,
                type_def,
                ..
            } = kind.as_ref()
            {
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
    let operators: Vec<&str> = sorted
        .iter()
        .copied()
        .filter(|n| is_operator_name(n))
        .collect();
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
        Sexp::Annotated {
            annotation,
            subject,
            ..
        } => format!(":{} {}", format_sexp(annotation), format_sexp(subject)),
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
    /// Canonical home of a trait/type NAME for the impl-confirmation line
    /// (FIXME 0671) — resolves against the current REPL module + prelude fallback,
    /// falling back to `fallback` when unresolvable. See [`impl_line_home_for`].
    fn impl_line_home(&self, name: &str, fallback: &ModuleFullPath) -> ModuleFullPath {
        impl_line_home_for(
            &self.shared.symbol_tables,
            &self.shared.prelude_fallback,
            &self.current_module_path(),
            name,
            fallback,
        )
    }

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
            ModuleEntry::Def {
                scheme, docstring, ..
            } => (Some(scheme.clone()), docstring.clone()),
            ModuleEntry::SpecialForm {
                scheme, docstring, ..
            } => (Some(scheme.clone()), docstring.clone()),
            ModuleEntry::TraitDecl { docstring, .. } => (None, docstring.clone()),
            _ => (None, None),
        };
        let source = self
            .shared
            .introspection
            .as_ref()
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
            EvalResult::Def { symbol, .. } => {
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
                            // FIXME 0671: qualify the trait and the type each by
                            // its CANONICAL HOME, not the asking module.
                            let trait_home = self.impl_line_home(trait_name, module);
                            let type_home = self.impl_line_home(target_type, module);
                            doc.plain("impl ");
                            push_fq_name(&mut doc, &trait_home, trait_name);
                            doc.plain(" for ");
                            push_fq_name(&mut doc, &type_home, target_type);
                        } else {
                            push_fq_name(&mut doc, &symbol.module, symbol.symbol.as_ref());
                            doc.plain(" ");
                            push_metadata(&mut doc, "; defined");
                        }
                        return doc;
                    }
                };
                // FIXME 0647: a trait's empty `; impl:` section is omitted for
                // BOTH the definition echo and the bare lookup (matching the
                // deftype `; match:` precedent); no bare-lookup-vs-echo flag.
                let mut body = self.format_def_entry_doc(&entry, name, &resolved_module);
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
                        inner_value,
                        &inner_type,
                        &self.shared.symbol_tables,
                    )
                } else {
                    crate::display::result_value_doc(*value, ty, &self.shared.symbol_tables)
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
    ) -> String {
        render(&self.format_def_entry_doc(entry, name, module))
    }

    /// Build the `:Type module/name ; classification` introspection `StyledDoc`
    /// (spec §1.1, §4.1) — R4 type annotation, R7 module prefix, R6 metadata.
    ///
    /// FIXME 0647: the former `full_trait_sections` flag (0542 — force an EMPTY
    /// `; impl:` drawer on bare trait lookup) is RETIRED; a trait's empty
    /// `; impl:` section is now omitted uniformly (echo and lookup agree, matching
    /// the `deftype` `; match:` precedent).
    pub(crate) fn format_def_entry_doc(
        &self,
        entry: &ModuleEntry<Code>,
        name: &str,
        module: &ModuleFullPath,
    ) -> StyledDoc {
        match entry {
            ModuleEntry::Def {
                scheme,
                kind,
                docstring,
                ..
            } => {
                match kind.as_ref() {
                    // Multi-sig: emit one line per variant per repl/spec.md
                    // §1.3 + §4.1.1.
                    DefKind::Overloaded { variants } if !variants.is_empty() => {
                        // D1 (traits.md §7.0.2): render each variant from its
                        // recorded template `Scheme` (constraints intact), keyed
                        // by `mangled_name` in this module's OWN table. `entry` is
                        // an OWNED clone here (not borrowed from the table), so the
                        // read guard cannot deadlock against it.
                        let module_table = self.shared.symbol_tables.get(module);
                        return format_overloaded_variants_doc(
                            name,
                            module,
                            variants,
                            docstring.as_deref(),
                            module_table.as_deref(),
                        );
                    }
                    DefKind::Constructor {
                        type_name,
                        type_def,
                        ..
                    } => {
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
                                    &self.shared.symbol_tables,
                                    module,
                                    &tn,
                                )
                            });
                            match info {
                                Some(info) => {
                                    crate::display::format_ctor_display(&tn, bare_ctor, &info)
                                }
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
                            name,
                            clauses_meta,
                            docstring.as_deref(),
                            module,
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
                push_metadata(
                    &mut doc,
                    classification_metadata(classification, docstring.as_deref()),
                );
                doc
            }
            ModuleEntry::SpecialForm {
                scheme,
                description,
                ..
            } => format_special_form_display_doc(name, scheme, description),
            ModuleEntry::TypeDef { .. } => self.format_type_display_doc(name, module),
            ModuleEntry::TraitDecl { docstring, .. } => {
                // 0558 (S108, resolve-home-enumeration.md §5): pass the RESOLVED
                // HOME `module` (the fn param, produced by the gate) so the trait
                // sections root at the home — where the `TraitDecl` is local
                // (depth 0) and the prelude outer-scope question cannot arise.
                self.format_trait_display_doc(name, docstring.as_deref(), module)
            }
            _ => {
                // TraitImpl entries have `Trait.Type` symbol names and
                // aren't stored in the symbol table as named entries.
                let mut doc = StyledDoc::new();
                if let Some((trait_name, target_type)) = name.split_once('.') {
                    // FIXME 0671: qualify the trait and the type each by its
                    // CANONICAL HOME, not the asking module `module`.
                    let trait_home = self.impl_line_home(trait_name, module);
                    let type_home = self.impl_line_home(target_type, module);
                    doc.plain("impl ");
                    push_fq_name(&mut doc, &trait_home, trait_name);
                    doc.plain(" for ");
                    push_fq_name(&mut doc, &type_home, target_type);
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
                        Some(module_table) => match module_table.get(source.symbol.as_ref()) {
                            Some(resolved) => {
                                let next = resolved.clone();
                                cur_module = source.module.clone();
                                cur_entry = next;
                                continue;
                            }
                            None => return (cur_entry, cur_module),
                        },
                        None => return (cur_entry, cur_module),
                    }
                }
                _ => return (cur_entry, cur_module),
            }
        }
        // Depth exhausted — return the last resolved entry/module.
        (cur_entry, cur_module)
    }
}

#[cfg(test)]
mod collect_related_tests {
    use super::*;

    use cranelisp_types::{FQTypeName, ModuleFullPath, Scheme, TypeDefInfo, TypeName, Visibility};
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
            "+", "-", "abs", "add", "ceil", "cons", "drop", "each", "map", "nth", "when", "zip",
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
    use crate::repl::test_support::*;

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
        assert!(
            !out.contains("codegen error"),
            "no codegen wrapper; got: {out}"
        );
        assert!(
            !out.contains("runtime panic:"),
            "no slot prefix; got: {out}"
        );
        assert!(!out.contains("0..0"), "no synthetic span; got: {out}");
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
        push_metadata(
            &mut doc,
            classification_metadata("defn", Some("Multiply by 2")),
        );
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
        let out = render(&format_related_section_doc(
            "match",
            &["Red", "Green", "Blue"],
        ));
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
        assert!(
            !buf["\x1b[1mFns:\x1b[0m\n".len()..].contains('\u{1b}'),
            "body plain: {buf:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// FIXME 0671 — the impl-confirmation line qualifies the trait and the type each
// by its CANONICAL HOME, not the asking module (resolve-home-enumeration.md §3
// rule-1; P24 "resolve once", P26 read the settled home).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod impl_line_home_tests {
    use super::*;
    use cranelisp_types::{Scheme, Type, UserFnState, Visibility};
    use std::collections::HashMap;

    fn tables() -> dashmap::DashMap<ModuleFullPath, SessionSymbolTable> {
        dashmap::DashMap::new()
    }
    fn ensure(t: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>, p: &str) {
        let path = ModuleFullPath::from(p);
        t.entry(path.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(path));
    }
    fn scheme() -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        }
    }
    fn public_def(
        t: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
        module: &str,
        name: &str,
    ) {
        let entry = ModuleEntry::def(
            scheme(),
            DefKind::UserFn {
                fn_state: UserFnState::NotDetermined,
            },
        )
        .visibility(Visibility::Public)
        .build();
        t.get_mut(&ModuleFullPath::from(module))
            .unwrap()
            .insert(Symbol::from(name), entry);
    }
    fn public_import(
        t: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
        importer: &str,
        name: &str,
        src_mod: &str,
    ) {
        let entry = ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from(src_mod),
                symbol: Symbol::from(name),
            },
            visibility: Visibility::Public,
        };
        t.get_mut(&ModuleFullPath::from(importer))
            .unwrap()
            .insert(Symbol::from(name), entry);
    }

    // The 0671 repro shape: `Display` (homed in text.display, imported into user)
    // resolves to text.display; `W` (defined in user) resolves to user. The asking
    // module `user` is NEVER stamped on `Display`.
    // spec: repl/spec.md §1.3 — impl line qualifies by canonical home.
    #[test]
    fn impl_line_home_resolves_imported_trait_to_defining_module() {
        let t = tables();
        ensure(&t, "text.display");
        ensure(&t, "user");
        public_def(&t, "text.display", "Display"); // Display's real home
        public_import(&t, "user", "Display", "text.display"); // user imports it
        public_def(&t, "user", "W"); // W is user-defined
        let pf = cranelisp_typecheck::PreludeFallback::default();
        let user = ModuleFullPath::from("user");

        let trait_home = impl_line_home_for(&t, &pf, &user, "Display", &user);
        let type_home = impl_line_home_for(&t, &pf, &user, "W", &user);
        assert_eq!(
            trait_home,
            ModuleFullPath::from("text.display"),
            "Display's canonical home is text.display, not the asking module"
        );
        assert_eq!(
            type_home,
            ModuleFullPath::from("user"),
            "W's canonical home is user"
        );
    }

    // Prelude-provided name (Int) resolves through the fallback to its home
    // (primitives), not the asking module.
    // spec: repl/spec.md §1.3 — prelude-provided type home.
    #[test]
    fn impl_line_home_resolves_prelude_provided_name_to_home() {
        let t = tables();
        ensure(&t, "primitives");
        ensure(&t, "prelude");
        ensure(&t, "user");
        public_def(&t, "primitives", "Int");
        public_import(&t, "prelude", "Int", "primitives"); // prelude re-exports Int
        let pf = cranelisp_typecheck::PreludeFallback::default();
        pf.insert(ModuleFullPath::from("user"), true); // user's fallback bit ON
        let user = ModuleFullPath::from("user");

        let home = impl_line_home_for(&t, &pf, &user, "Int", &user);
        assert_eq!(
            home,
            ModuleFullPath::from("primitives"),
            "Int resolves through the prelude fallback to primitives, not user"
        );
    }

    // An unresolvable name falls back to the asking module (no worse than the old
    // behaviour) — the fix must not regress the genuinely-unknown case.
    // spec: repl/spec.md §1.3 — fallback for unresolved.
    #[test]
    fn impl_line_home_falls_back_when_unresolved() {
        let t = tables();
        ensure(&t, "user");
        let pf = cranelisp_typecheck::PreludeFallback::default();
        let user = ModuleFullPath::from("user");
        let home = impl_line_home_for(&t, &pf, &user, "Nonexistent", &user);
        assert_eq!(
            home, user,
            "an unresolvable name falls back to the asking module"
        );
    }
}
