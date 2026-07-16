//! Per-kind introspection-display producers — the `*_display`/`*_display_doc`
//! family that renders a *named definition* (type, trait, builtin type, special
//! form, macro, overloaded fn) for `/info`/`/sig`/`/doc`/`/type`, plus the
//! `; defn:`/`; impl:`/`; match:` related-section builders they share. The
//! type-level sibling of the value-echo renderers in `repl/format.rs`; consumes
//! the shared resolution toolbox in `repl/mod.rs`. A-split of `repl/format.rs`
//! per `design/int/repl-decomposition.md` §1.6.1 (FIXME 0627); pure relocation,
//! behaviour-invariant.


use super::*;


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

impl CompilerSession {
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

#[cfg(test)]
mod fq_arg_format_type_tests {
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
