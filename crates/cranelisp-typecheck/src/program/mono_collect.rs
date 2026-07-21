use super::*;

/// A polymorphic fn-value passed as an argument into a HOF, recorded per
/// enclosing defn for post-mint `Var` rewrite (FIXME 0374 / 0488 sig b):
/// (enclosing_defn, bare_fn_value_symbol, arg_span, concrete_param_types,
/// home_of_imported_callee).
type FnValueArgSite = (Symbol, Symbol, Span, Vec<Type>, Option<ModuleFullPath>);


/// A monomorphisation call site collected by `pass4_monomorphise`:
/// (callee_name, arg_spans, call_span, home_of_imported_callee).
type MonoCallSite = (Symbol, Vec<Span>, Span, Option<ModuleFullPath>);


/// The body expressions a mono-collect scan must walk for one `Defn`.
///
/// A single-sig defn contributes its one body; a MULTI-sig defn contributes each
/// clause variant's body (§11.8.3 leg D3 — NEVER `defn.body()`, which asserts
/// single-variant and panics on a multi-sig defn, `cranelisp-types/src/ast.rs`).
/// The `MultiSig` harvest runs post-`finalize_multi_sig_variant_types` so every
/// clause is settled concrete before its body is scanned. The base defn name is
/// the self-exclusion key in either case (a clause's own `(build …)` self-call is
/// overloaded-base dispatch handled by the drain, not a mono leaf).
fn mono_scan_bodies(defn: &Defn) -> Vec<&Expr> {
    if defn.is_multi_sig() {
        defn.variants.iter().map(|v| &v.body).collect()
    } else {
        vec![defn.body()]
    }
}

/// The settlement discipline a `resolve_auto_curry` drain runs under (S115 W4).
///
/// The auto-curry drain runs at SIX seams, and they are not equivalent: the
/// per-form body drains fire while later forms may still pin the operand type,
/// whereas the finalize drain runs post-drain/post-Phase-A on settled state.
/// Only a settled drain may conclude "this trait operator has no impl to
/// dispatch to"; a pre-settlement one must hold the entry back rather than
/// transport the trait-method DECLARATION FQ as a dispatch carrier
/// (`design/backend/s115-carrier-and-rc-sweep.md` §1.3 — the `'='` face).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AutoCurryDrain {
    /// A pre-settlement seam (per-form / per-variant body post-pass). An
    /// operator whose only available carrier is a trait-method-decl FQ is
    /// pushed to `CheckState::deferred_auto_curry` for the settled retry.
    Deferrable,
    /// A settled or recheck-scoped seam (finalize; impl-method and mono-body
    /// rechecks, whose resolution maps and module scope are swapped so nothing
    /// may be deferred out of them). No entry is held back.
    Final,
}

// --- Name mangling for multi-sig overload dispatch ---



impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Monomorphise every reachable polymorphic / constrained call site into
    /// concrete instances.
    ///
    /// Returns the `Vec<MonoDefn>` (each carrying a `Defn` body the backend
    /// still reads pre-Phase-3). S84 Phase-3 (FIXME 0392): the concrete-boundary
    /// `MonoExpr` view of every instance is now set ON the instance's
    /// `ModuleEntry::Def.codegen_view` at `register_mono_entry` (the single
    /// source of truth, Principle 7) — the transitional parallel
    /// `CheckState.mono_variants` `Vec` that carried it is retired. The
    /// `MonoExpr::from_expr` validation (a residual `Var` in any instance
    /// surfaces as a §3.11.1 could-not-monomorphise error) runs at the
    /// `monomorphise_call` seam, unchanged.
    pub(super) fn pass4_monomorphise(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
        constrained_fn_names: &HashSet<Symbol>,
    ) -> Result<Vec<MonoDefn>, CranelispError> {
        let (call_sites, fn_value_arg_sites) =
            self.collect_mono_call_sites(state, defns, constrained_fn_names);

        // Nothing to monomorphise (neither local constrained fns nor imported
        // constrained call sites nor polymorphic fn-value arguments) — bail
        // before resolving expr_types.
        if call_sites.is_empty() && fn_value_arg_sites.is_empty() {
            return Ok(Vec::new());
        }

        // Resolve expr_types so we can look up concrete arg types
        let resolved_expr_types = self.resolve_expr_types(state);

        // Monomorphise each call site and record dispatch mappings
        let mut mono_defns = Vec::new();
        let mut seen: HashMap<String, JitSymbol> = HashMap::new();
        // The caller's module — the fallback home for a LOCAL generic's mono
        // name. `monomorphise_call` restores `state.current_module` per call, so
        // capturing once here is stable across the loop (FIXME 0519).
        let current_module = state.current_module.clone();

        self.drive_call_site_monomorphisation(
            state,
            &call_sites,
            &resolved_expr_types,
            &current_module,
            &mut seen,
            &mut mono_defns,
        )?;

        let fn_value_rewrites = self.drive_fn_value_monomorphisation(
            state,
            &fn_value_arg_sites,
            &current_module,
            &mut seen,
            &mut mono_defns,
        )?;

        // Apply the fn-value `Var` renames to the stored ASTs. A later
        // re-annotation pass (in `finalize_check_result_inner`) only writes
        // `inferred_type` / `resolved_call` by span — it does not touch the
        // `Var` name — so this rename survives.
        if !fn_value_rewrites.is_empty() {
            let mut st = self.current_symbol_table_mut(state);
            for (enclosing, arg_span, mangled_sym) in &fn_value_rewrites {
                if let Some(ModuleEntry::Def { ast: Some(variant), .. }) =
                    st.symbols.get_mut(enclosing)
                {
                    rename_var_at_span(&mut variant.body, *arg_span, mangled_sym);
                }
            }
            drop(st);
            // S110 W0.1b (§1.1.1, fn-value mono-rewrite carrier): the rename
            // repoints the arg-position `Var` at the caller-local mangled mono,
            // but the span-keyed carrier still names the slot-less template (or
            // is absent). Update the sidecar to the minted instance's STORAGE
            // identity — the caller's module (`register_mono_entry` registers
            // the mono in `current_module`, even for an imported generic whose
            // mangle embeds its home). Without this, the W2 0585 keyed read
            // would hard-fail this VALID program on the stale template carrier.
            for (_enclosing, arg_span, mangled_sym) in &fn_value_rewrites {
                // Arg-position fn-value `Var` → the minted instance's storage FQ
                // (a table reference: `VarRef::Global`). S114 carrier flip.
                state.method_resolutions.var_refs.insert(
                    *arg_span,
                    cranelisp_types::VarRef::Global(FQSymbol {
                        module: current_module.clone(),
                        symbol: mangled_sym.clone(),
                    }),
                );
            }
        }

        // S84 Phase-3 (FIXME 0392): the concrete-boundary `MonoExpr` view of
        // each minted instance is now set ON its `ModuleEntry::Def.codegen_view`
        // at `register_mono_entry` — no parallel `Vec` to drain.
        Ok(mono_defns)
    }


    /// Collect the Pass-4 monomorphisation work list from every defn body
    /// (`program-decomposition.md` §2.2): local constrained calls, imported
    /// constrained/parametric calls, local pure-parametric hops, and
    /// polymorphic fn-value arguments. Returns `(call_sites, fn_value_arg_sites)`.
    pub(super) fn collect_mono_call_sites(
        &self,
        state: &mut CheckState,
        defns: &[&Defn],
        constrained_fn_names: &HashSet<Symbol>,
    ) -> (Vec<MonoCallSite>, Vec<FnValueArgSite>) {
        // Collect call sites: (fn_name, arg_spans, call_span, home_module).
        //
        // `home_module` is `None` for a call to a LOCALLY-defined constrained fn
        // (`monomorphise_call` re-checks its body in the current module's scope,
        // the as-built path). It is `Some(home)` for a call to an IMPORTED
        // constrained fn that chain-resolves to a constrained `Def` in another
        // module — the mono body must be re-checked in that DEFINING module's
        // import context, where its trait-method + helper references resolve
        // (FIXME 0355; the feature half of the resolved 0354 SIGSEGV).
        //
        // FIXME 0349 — scan EVERY defn body, including those that are themselves
        // in `constrained_fn_names`. A constrained/polymorphic defn can still
        // host a *concrete* call to another constrained fn that needs a mono
        // variant. Under forward-reference ordering a caller (`main`) can stay
        // spuriously polymorphic (its result var never pinned because the callee
        // it forward-references was generalized before the helper that ties its
        // accumulator) and thus land in `constrained_fn_names`; skipping its body
        // wholesale meant the `(reduce add-i64 0 [1 2 3])` call site was never
        // collected and `reduce$Int+Vec` was never created — so `main` called the
        // polymorphic template and returned the initial accumulator (0344/0349).
        // We must NOT skip such bodies; we only skip a call from a fn to ITSELF
        // (the generic self-recursion of a constrained defn is not a concrete
        // call site — its arg types are the defn's own generic vars).
        let mut local_calls = Vec::new();
        for defn in defns {
            for body in mono_scan_bodies(defn) {
                Self::collect_constrained_calls_excluding_self(
                    body,
                    &defn.name,
                    constrained_fn_names,
                    &state.method_resolutions.var_refs,
                    &mut local_calls,
                );
            }
        }
        let mut call_sites: Vec<MonoCallSite> = local_calls
            .into_iter()
            .map(|(name, spans, span)| (name, spans, span, None))
            .collect();

        // FIXME 0355 — collect call sites for IMPORTED callees that
        // chain-resolve to a constrained (or pure-parametric) `Def` in another
        // module. These are NOT in `constrained_fn_names` (their local name is a
        // `ModuleEntry::Import`), so the local collection above never sees them.
        for defn in defns {
            for body in mono_scan_bodies(defn) {
                self.collect_imported_constrained_calls(
                    state,
                    body,
                    constrained_fn_names,
                    &mut call_sites,
                );
            }
        }

        // FIXME 0373 (Tier 1, /arch ruling (A) — monomorphise polymorphic-result
        // hops) — collect call sites for LOCAL (same-module) pure-parametric
        // polymorphic callees. These are NOT in `constrained_fn_names` (that set
        // holds only trait-constrained fns — `detect_constrained_fns` keys on
        // `UserFnState::Constrained`), and they live in the current module so the
        // imported-call pass above (which requires `home != current_module`)
        // skips them too. Yet a hop like `(defn h1 [f] (h2 f))` whose RESULT type
        // generalizes to an unbound `Type::Var` is compiled ONCE generically
        // (program.rs §919 "generalize-and-keep-a-single-generic Concrete slot"),
        // leaving its result `Type::Var` at codegen. The backend's RC classifier
        // (`HeapCategory::classify(Type::Var) -> Mixed`) then emits a guarded
        // RC-inc whose `< 1024` immediate-vs-pointer heuristic mis-reads a
        // negative / large Int result as a heap pointer and dereferences it →
        // SIGSEGV (FIXME 0373 root-cause). Monomorphising the hop at the concrete
        // instantiation reached from its call site gives the mono instance a
        // CONCRETE result type (`Int`) → `classify` sees `NeverHeap` → no guard →
        // no crash. This reuses the same 0355 collection + `monomorphise_call` +
        // caller-GOT-slot mechanism, widening the trigger from "constrained /
        // imported callee" to "polymorphic-result hop reached at a concrete type".
        for defn in defns {
            for body in mono_scan_bodies(defn) {
                self.collect_local_parametric_calls(
                    state,
                    body,
                    &defn.name,
                    constrained_fn_names,
                    &mut call_sites,
                );
            }
        }

        // FIXME 0374 (Tier 2 — the `(Box a)`-field-through-HOF gap). Collect
        // bare-`Var` ARGUMENTS that pass a monomorphisable polymorphic fn as a
        // VALUE into a higher-order call. These are not callees (so the
        // call-site collectors above miss them) but they still need a concrete
        // mono instance — see `collect_parametric_fn_value_args`. Recorded
        // per enclosing defn so the fn-value `Var` can be rewritten to the
        // mangled name in that defn's stored AST after minting.
        let mut fn_value_arg_sites: Vec<FnValueArgSite> = Vec::new();
        for defn in defns {
            for body in mono_scan_bodies(defn) {
                let mut sites = Vec::new();
                self.collect_parametric_fn_value_args(state, body, &mut sites);
                for (arg_name, arg_span, param_types, home) in sites {
                    fn_value_arg_sites.push((defn.name.clone(), arg_name, arg_span, param_types, home));
                }
            }
        }

        (call_sites, fn_value_arg_sites)
    }


    /// Drive monomorphisation over the collected call sites
    /// (`program-decomposition.md` §2.2): re-derive each site's concrete arg
    /// types from the final `resolved_expr_types`, dedup by the canonical
    /// mangled name, mint the mono instance via `monomorphise_call`, and record
    /// the `SigDispatch`. Threads `seen` / `mono_defns` shared with the fn-value
    /// pass.
    pub(super) fn drive_call_site_monomorphisation(
        &self,
        state: &mut CheckState,
        call_sites: &[MonoCallSite],
        resolved_expr_types: &HashMap<Span, Type>,
        current_module: &ModuleFullPath,
        seen: &mut HashMap<String, JitSymbol>,
        mono_defns: &mut Vec<MonoDefn>,
    ) -> Result<(), CranelispError> {
        for (fn_name, arg_spans, call_span, home_module) in call_sites {
            // Look up concrete arg types from resolved expr_types
            let arg_types: Vec<Type> = arg_spans
                .iter()
                .filter_map(|span| resolved_expr_types.get(span).cloned())
                .collect();

            if arg_types.len() != arg_spans.len() {
                // Missing type info for some args — skip this call site
                continue;
            }

            // ALL-ARGS-CONCRETE GUARD (Phase-4 part A, concrete-boundary-type.md
            // §4-A). The collection-time trigger (`local_parametric_call_triggers`)
            // gates on `state.subst`-resolved `expr_types`, but the actual arg
            // types are re-derived HERE from the FINAL `resolved_expr_types` — and
            // a call collected from a GENERIC caller's body (the
            // `(reduce-loop f init v (vec-len v) 0)` call inside `reduce`'s body,
            // while `reduce` is still generic) resolves here to the parent's OWN
            // free scheme vars (`[Fn[Var,Var]→Var, Var, (Vec Var), Int, Int]`).
            // Monomorphising that mints the SPURIOUS partial `reduce-loop$Vec+Int+Int`
            // (lossy name, residual body vars). The genuine concrete instance is
            // minted via the parent's CONCRETE re-check chain
            // (`reduce$Int+Vec → reduce-loop$Int+Vec+Int+Int`) — its args ARE all
            // concrete. Skip any site whose final arg types are not all concrete:
            // every minted instance is then fully concrete (the carve-out is dead,
            // `from_expr` succeeds on each — the completeness proof).
            if !arg_types.iter().all(|t| t.is_concrete()) {
                continue;
            }

            // Deduplicate: same defining home + fn + arg types = same
            // specialization. Route the dedup key through the ONE canonical
            // mangler so the dedup grain == the minted-name grain (FIXME 0519):
            // a home-blind key collapsed two same-named imported generics at the
            // dedup step (the 0508 collapse point) even after the name grew a
            // home. `arg_types` are the concrete param types (gated concrete
            // above), so this key string is byte-identical to the `mono.defn.name`
            // that `monomorphise_call` mints below.
            let key_home = home_module
                .clone()
                .unwrap_or_else(|| current_module.clone());
            let key = crate::traits::build_mangled_name(&key_home, fn_name, &arg_types);

            if let Some(mangled) = seen.get(&key) {
                // Already generated this specialization — just record dispatch
                let resolution =
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() };
                self.record_dispatch_target(state, *call_span, &resolution);
                state.method_resolutions.resolved_calls.insert(*call_span, resolution);
                continue;
            }

            if let Some(mono) = self.monomorphise_call(
                state, fn_name, &arg_types, *call_span, home_module.as_ref(), None,
            )? {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                // Record dispatch for this call site
                let resolution =
                    ResolvedCall::SigDispatch { mangled_name: mangled.clone() };
                self.record_dispatch_target(state, *call_span, &resolution);
                state.method_resolutions.resolved_calls.insert(*call_span, resolution);
                seen.insert(key, mangled);
                mono_defns.push(mono);
            }
        }

        Ok(())
    }


    /// Drive monomorphisation of polymorphic fn-value arguments
    /// (`program-decomposition.md` §2.2, FIXME 0374 Tier 2): mint each site's
    /// concrete mono instance and collect the `(enclosing, arg_span, mangled)`
    /// rewrites the driver applies to the stored ASTs. Shares `seen` /
    /// `mono_defns` with the call-site pass.
    pub(super) fn drive_fn_value_monomorphisation(
        &self,
        state: &mut CheckState,
        fn_value_arg_sites: &[FnValueArgSite],
        current_module: &ModuleFullPath,
        seen: &mut HashMap<String, JitSymbol>,
        mono_defns: &mut Vec<MonoDefn>,
    ) -> Result<Vec<(Symbol, Span, Symbol)>, CranelispError> {
        // FIXME 0374 (Tier 2 — fn-value-argument monomorphisation). For each
        // polymorphic fn passed as a value into a HOF, mint its concrete mono
        // instance (`mk$Int`) and rewrite the fn-value `Var` in the enclosing
        // defn's stored AST to the mangled name, so the backend's
        // `compile_fn_as_value` takes the concrete (slotted) instance's GOT slot
        // rather than the slot-less `Polymorphic` template. The mono instance's
        // body re-checks at the concrete param types, so its `(Box a)` field
        // becomes `(Box Int)` — concrete, classifying cleanly, no RC guard.
        let mut fn_value_rewrites: Vec<(Symbol, Span, Symbol)> = Vec::new();
        for (enclosing, arg_name, arg_span, param_types, home) in fn_value_arg_sites {
            // Home-qualified dedup key == the minted name (FIXME 0519): `home`
            // for an IMPORTED generic fn-value (FIXME 0488 sig b), else current.
            let key_home = home
                .clone()
                .unwrap_or_else(|| current_module.clone());
            let key = crate::traits::build_mangled_name(&key_home, arg_name, param_types);
            let mangled_sym = if let Some(existing) = seen.get(&key) {
                Symbol::from(existing.as_ref())
            } else if let Some(mono) =
                // Pass `Span::SYNTHETIC` as the call-span: a fn-VALUE argument is
                // not a call site, so the FIXME-0349 call-result propagation
                // inside `monomorphise_call` (which unifies the call-span's
                // expr-type with the mono's RETURN type) must NOT fire — the
                // arg-span's type is the fn's FULL `(Fn ..)` type, not its
                // return. A synthetic span misses the `expr_types` lookup and
                // skips that unify cleanly. `home` is `Some(defining_module)` for
                // an IMPORTED generic fn-value (FIXME 0488 sig b), `None` local.
                self.monomorphise_call(
                    state, arg_name, param_types, Span::SYNTHETIC, home.as_ref(), None,
                )?
            {
                let mangled = JitSymbol::from(mono.defn.name.as_ref());
                seen.insert(key, mangled.clone());
                let sym = Symbol::from(mangled.as_ref());
                mono_defns.push(mono);
                sym
            } else {
                continue;
            };
            fn_value_rewrites.push((enclosing.clone(), *arg_span, mangled_sym));
        }

        Ok(fn_value_rewrites)
    }


    /// Walk a defn body collecting calls to IMPORTED callees that chain-resolve
    /// to a constrained (trait-bound) or pure-parametric polymorphic `Def` in
    /// another module (FIXME 0355).
    ///
    /// A locally-defined constrained fn is named in `constrained_fn_names` and is
    /// already collected by [`Self::collect_constrained_calls_excluding_self`];
    /// here we skip those and look only at bare `Var` callees whose local name
    /// chain-resolves (via [`Self::resolve_terminal_entry_and_home`]) to a
    /// terminal in a DIFFERENT module. When that terminal is a constrained or
    /// still-polymorphic `UserFn` `Def`, the call needs a cross-module mono
    /// variant re-checked in the terminal's HOME scope, so we record the call
    /// site with `Some(home)`.
    pub(super) fn collect_imported_constrained_calls(
        &self,
        state: &CheckState,
        expr: &Expr,
        constrained_fn_names: &HashSet<Symbol>,
        out: &mut Vec<(Symbol, Vec<Span>, Span, Option<ModuleFullPath>)>,
    ) {
        // DEF-1 (S86): resolve the bare callee through the **prelude-fallback**
        // scope resolve (`resolve_terminal_fq_scoped`), NOT the
        // current-module-only `resolve_terminal_entry_and_home`. A polymorphic fn
        // provided ONLY via the implicit prelude (an implicit `(import [prelude
        // [*]])`, no explicit import) is invisible to a current-module-rooted
        // lookup, so its concrete mono was never minted in the consuming module →
        // codegen `undefined function`. The fallback-aware resolver applies the
        // same I-1 public-only filter the value/type/ctor/trait chokepoints use,
        // and reports the terminal `home` (the prelude — `!= current_module`), so
        // the cross-module mono path fires exactly as it does for the
        // explicit-import control (S78 prelude-fallback discipline; the
        // mono-collection chokepoint had been missed).
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            // FIXME 0653 — skip a §4.6 LOCAL shadow (see collect_local_parametric_calls).
            && callee_has_keyed_carrier(&state.method_resolutions.var_refs, callee.span())
            && !constrained_fn_names.contains(name)
            && let Some(resolved) = self.resolve_terminal_fq_scoped(state, name.as_ref())
            && resolved.home != state.current_module
            && Self::entry_is_monomorphisable_polymorphic(&resolved.entry)
        {
            // FIXME 0488 sig a (cross-module FQ): record the BARE terminal symbol
            // (`resolved.fq.symbol`), not the raw reference `name` — a qualified
            // callee (`gen/iden2`) would otherwise reach `get_constrained_fn`'s
            // home-probe as a `/`-bearing key in the home module → no mint. The
            // resolver already split `mod/sym` and resolved the module alias.
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((resolved.fq.symbol.clone(), arg_spans, *span, Some(resolved.home)));
        }
        for_each_child_expr(expr, |child| {
            self.collect_imported_constrained_calls(state, child, constrained_fn_names, out)
        });
    }


    /// Whether a call site to a LOCAL polymorphic callee should be collected for
    /// monomorphisation. ONE predicate: **every argument is fully concrete**
    /// (Phase-4 part A, Option 1, concrete-boundary-type.md §4-A — collapsing the
    /// former two triggers).
    ///
    /// A mono instance is minted **iff every argument type is concrete**; its
    /// result is then concrete by the per-instance re-check (the body re-check +
    /// `unify(body_ty, ret_ty)` pins the result). This subsumes BOTH the old
    /// 0373 result-hop trigger (`result_is_bare_var`) and the 0374
    /// direct-concrete-call trigger:
    ///
    /// - **Genuine result hops (0373) are still minted** — a result-bare-var hop
    ///   whose ARGS are concrete (`(g 1)`, `(h2 x)` with `x: Int`) passes this
    ///   predicate; the body re-check pins the result. The genuine concrete
    ///   result-hop arrives here through the parent's concrete re-check chain
    ///   with every arg already pinned.
    /// - **Direct concrete calls (0374)** — `(g 1)` with `g : ∀a. a→a` passes:
    ///   all args concrete, so the `g$Int` instance is minted (`g` is slot-less
    ///   under the structural slot gate; an un-monomorphised call would lower
    ///   through a missing slot).
    /// - **The SPURIOUS partial result-hop is EXCLUDED** — a result-bare-var hop
    ///   whose args are still the parent's free scheme vars (the `reduce →
    ///   reduce-loop` 0344 fold inner call, where `f`/`acc`/element are
    ///   `reduce`'s OWN `Var34`/`Var31`) fails the all-args-concrete predicate,
    ///   so no partial `reduce-loop$Vec+Int+Int` is minted. The genuine concrete
    ///   `reduce-loop$Int+Vec+Int+Int` is minted via the concrete `reduce$Int+Vec`
    ///   chain (where the args ARE pinned), unaffected.
    ///
    /// **The 0344 fold is preserved by the all-args-concrete guard.** The fold
    /// call `(reduce vec-push [] vv)` has args `vec-push` (a polymorphic
    /// fn-VALUE), `[]` (`(Vec a)`), `vv` — NOT all concrete — so it is excluded.
    /// Monomorphising it would pin `reduce`'s accumulator var through the
    /// post-mono regeneralisation, re-collapsing the polymorphic scheme 0344
    /// deliberately keeps; the all-concrete guard keeps it out.
    ///
    /// An empty-arg call does NOT trigger (a nullary polymorphic call cannot be
    /// pinned by its args — if its result is concrete it needs no mono; if its
    /// result is a free var it is the ambiguity case, §2.6, not a mono site).
    pub(super) fn local_parametric_call_triggers(
        state: &CheckState,
        _call_span: &Span,
        args: &[Expr],
    ) -> bool {
        !args.is_empty()
            && args.iter().all(|a| {
                state
                    .expr_types
                    .get(&a.span())
                    .map(|ty| apply(&state.subst, ty).is_concrete())
                    .unwrap_or(false)
            })
    }


    /// Walk a defn body collecting calls to LOCAL (same-module) pure-parametric
    /// polymorphic callees that need a concrete monomorphisation (FIXME 0373,
    /// Tier 1 — the polymorphic-result-hop fix; /arch ruling (A)).
    ///
    /// Mirrors [`Self::collect_imported_constrained_calls`] for the *local* case:
    /// a trait-constrained local fn is already in `constrained_fn_names` and is
    /// collected by [`Self::collect_constrained_calls_excluding_self`]; here we
    /// pick up bare `Var` callees whose local name resolves (chain-follow) to a
    /// terminal in the SAME module that is a pure-parametric polymorphic `UserFn`
    /// `Def` (the `entry_is_monomorphisable_polymorphic` shape, excluding the
    /// already-collected constrained set). The call site is recorded with
    /// `home: None` (the same-module `monomorphise_call` path — recheck the body
    /// in the current module's scope). A call from a fn to ITSELF is skipped:
    /// generic self-recursion is the defn's own generic vars, not a concrete site.
    pub(super) fn collect_local_parametric_calls(
        &self,
        state: &CheckState,
        expr: &Expr,
        self_name: &Symbol,
        constrained_fn_names: &HashSet<Symbol>,
        out: &mut Vec<(Symbol, Vec<Span>, Span, Option<ModuleFullPath>)>,
    ) {
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && name != self_name
            // FIXME 0653 — skip a §4.6 LOCAL shadow: a callee whose `var_refs`
            // verdict is `VarRef::Local` (S114 carrier flip — was "no keyed
            // `resolved_targets` carrier") resolved to a let/fn/param binding
            // (the shadow gate declined a table target), NOT the top-level
            // parametric fn the name-scan would mint. The name is a trigger, not
            // the identity; `callee_has_keyed_carrier` returns TRUE only for a
            // `VarRef::Global` verdict.
            && callee_has_keyed_carrier(&state.method_resolutions.var_refs, callee.span())
            && !constrained_fn_names.contains(name)
            && Self::local_parametric_call_triggers(state, span, args)
            && let Some(resolved) = self.resolve_terminal_fq_scoped(state, name.as_ref())
            && resolved.home == state.current_module
            && Self::entry_is_monomorphisable_polymorphic(&resolved.entry)
        {
            // FIXME 0488 sig a (same-module FQ): resolve via the `/`-splitting
            // fallback resolver (the raw `resolve_terminal_entry_and_home` probe
            // keyed the qualified `test/iden` string and missed) and record the
            // BARE terminal symbol so `(test/iden 5)` mints/dispatches under the
            // same `iden$Int` name as the bare call. A cross-module qualifier
            // resolves with `home != current` and is left to the imported
            // collector; a prelude fn likewise (home == prelude != current).
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((resolved.fq.symbol.clone(), arg_spans, *span, None));
        }
        for_each_child_expr(expr, |child| {
            self.collect_local_parametric_calls(
                state, child, self_name, constrained_fn_names, out,
            )
        });
    }


    /// Walk a defn body collecting bare-`Var` ARGUMENTS that pass a
    /// monomorphisable polymorphic fn as a *value* into a higher-order call
    /// (FIXME 0374 — the `(Box a)`-field-carrying-`Type::Var`-through-HOF gap).
    ///
    /// The result-hop collectors ([`Self::collect_local_parametric_calls`] +
    /// [`Self::monomorphise_inner_parametric_hops`]) trigger on a bare-`Var`
    /// *call result* or an `Apply`-of-bare-`Var`. They do NOT cover a polymorphic
    /// fn passed as an argument value (`(thru mk x)` — `mk` is a fn-value
    /// argument, never a callee here, and the HOF call's result `(Box Int)` is
    /// concrete so the result-var gate skips it). That fn-value still needs a
    /// concrete mono instance: `mk`'s body constructs `(Box a)` with a `Type::Var`
    /// field that reaches the RC boundary as a non-concrete `Box` field →
    /// `classify(Type::Var)` → the unsound `<1024` guard → SIGSEGV.
    ///
    /// For each `Apply` whose bare-`Var` argument resolves (chain-follow) to a
    /// LOCAL monomorphisable polymorphic def AND whose resolved expr-type at the
    /// argument span is a FULLY CONCRETE `(Fn [..] ..)`, record
    /// `(arg_var_name, arg_span, concrete_param_types)`. The caller mints
    /// `arg_var$T..` and rewrites the fn-value `Var` in the enclosing defn's
    /// stored AST to the mangled name so the backend takes the concrete mono
    /// instance's GOT slot.
    pub(super) fn collect_parametric_fn_value_args(
        &self,
        state: &CheckState,
        expr: &Expr,
        out: &mut Vec<(Symbol, Span, Vec<Type>, Option<ModuleFullPath>)>,
    ) {
        // A generic fn referenced in VALUE position at a concrete `Fn` type
        // (FIXME 0374 fn-value monomorphisation; 0571 D1 extension; 0585 —
        // position-completeness cure). A value-position generic fn-value ref
        // reaches the backend slot-less unless monomorphised here ⇒ the
        // `undefined variable` codegen leak (0571 D1).
        //
        // **POSITION-COMPLETE (0585, mirroring `find_ambiguous_value_position`).**
        // The verdict must fire on EVERY codegen-reaching value position, not a
        // hand-picked whitelist. The old shape only visited `Apply { args }` and
        // `Let`/`ParBind` binding values, so a generic fn-value in an `if`
        // branch, a `match` arm body, a `VecLit` element, a ctor field, or a
        // `let` tail body slipped past collection and reached codegen slot-less.
        // `for_each_child_expr` is the single child-enumeration source of truth;
        // its children ARE the value positions. Only the `Apply` CALLEE is a
        // DISPATCH position (not a runtime value) — it mints through the ordinary
        // call-site path, so we recurse INTO it but never collect it as a
        // fn-value. `try_collect_parametric_fn_value` self-guards on
        // `Expr::Var`, so applying it to a non-`Var` child is a no-op.
        let callee_span = match expr {
            Expr::Apply { callee, .. } => Some(callee.span()),
            _ => None,
        };
        for_each_child_expr(expr, |child| {
            if Some(child.span()) != callee_span {
                self.try_collect_parametric_fn_value(state, child, out);
            }
            self.collect_parametric_fn_value_args(state, child, out);
        });
    }


    /// The per-`Var` fn-value monomorphisation collect (FIXME 0374 / 0488 sig b /
    /// 0571 D1) — records `(bare_symbol, ref_span, param_types, home)` for a
    /// value-position `Var` that resolves to a monomorphisable polymorphic fn
    /// whose full `Fn` signature is concrete at this reference. Shared by the HOF
    /// argument and let-binding value sites.
    pub(super) fn try_collect_parametric_fn_value(
        &self,
        state: &CheckState,
        var_expr: &Expr,
        out: &mut Vec<(Symbol, Span, Vec<Type>, Option<ModuleFullPath>)>,
    ) {
        if let Expr::Var { name, span, .. } = var_expr
            && let Some(ty) = state.expr_types.get(span)
            && let Type::Fn(param_types, ret_ty) = apply(&state.subst, ty)
            // The fn-value's full signature must be concrete — the instantiation
            // the use demands, and the shape that pins any residual ADT-field
            // `Type::Var`.
            && param_types.iter().all(|p| p.is_concrete())
            && ret_ty.is_concrete()
            && let Some(resolved) = self.resolve_terminal_fq_scoped(state, name.as_ref())
            && Self::entry_is_monomorphisable_polymorphic(&resolved.entry)
        {
            // Same-module ⇒ `home: None` (byte-identical to the 0374 path); an
            // IMPORTED generic fn-value carries its defining module so the mint
            // re-checks the body in the DEFINING scope (FIXME 0488 sig b). The
            // BARE terminal symbol keys the mangle + `rename_var_at_span` target.
            let home = if resolved.home == state.current_module {
                None
            } else {
                Some(resolved.home.clone())
            };
            out.push((resolved.fq.symbol.clone(), *span, param_types, home));
        }
    }


    /// Does this terminal entry need a monomorphised specialisation when called
    /// with concrete arg types? (FIXME 0355 — mirrors `get_constrained_fn`'s two
    /// accepted shapes: a trait-constrained `UserFn`, or a pure-parametric
    /// polymorphic `UserFn` carrying a stored annotated `ast`.)
    pub(crate) fn entry_is_monomorphisable_polymorphic(entry: &ModuleEntry<C>) -> bool {
        if let ModuleEntry::Def { kind, scheme, ast, .. } = entry {
            match kind.as_ref() {
                DefKind::UserFn { fn_state: UserFnState::Constrained(_) } => true,
                DefKind::UserFn { fn_state }
                    if !matches!(fn_state, UserFnState::Constrained(_))
                        && !scheme.type_vars.is_empty()
                        && ast.is_some() =>
                {
                    true
                }
                _ => false,
            }
        } else {
            false
        }
    }


    /// Recursively walk an expression tree collecting calls to constrained fns.
    ///
    /// Each call site is recorded as (fn_name, arg_spans, call_span).
    /// The arg_spans are the spans of each argument expression, used to look up
    /// their types from `expr_types`.
    pub(crate) fn collect_constrained_calls(
        expr: &Expr,
        constrained_fn_names: &HashSet<Symbol>,
        var_refs: &HashMap<Span, cranelisp_types::VarRef>,
        out: &mut Vec<(Symbol, Vec<Span>, Span)>,
    ) {
        // Per-node action: record a call site when this node is an Apply whose
        // callee is a bare reference to a constrained fn.
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && constrained_fn_names.contains(name)
            // FIXME 0653 — skip a §4.6 LOCAL shadow of a top-level constrained fn.
            && callee_has_keyed_carrier(var_refs, callee.span())
        {
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((name.clone(), arg_spans, *span));
        }
        // Recurse into children via the shared enumeration helper.
        for_each_child_expr(expr, |child| {
            Self::collect_constrained_calls(child, constrained_fn_names, var_refs, out)
        });
    }


    /// Like [`collect_constrained_calls`] but excludes calls a constrained fn
    /// makes to ITSELF (FIXME 0349).
    ///
    /// A constrained/polymorphic defn's self-recursion is the generic definition,
    /// not a concrete monomorphisation site — its argument types are the defn's
    /// own generic vars, so there is no concrete instantiation to specialise.
    /// Every OTHER constrained call inside the body (including calls to *other*
    /// constrained fns from within a constrained fn) IS a real call site and must
    /// be collected, so a forward-referenced helper gets its mono variant created
    /// regardless of source definition order.
    pub(super) fn collect_constrained_calls_excluding_self(
        expr: &Expr,
        self_name: &Symbol,
        constrained_fn_names: &HashSet<Symbol>,
        var_refs: &HashMap<Span, cranelisp_types::VarRef>,
        out: &mut Vec<(Symbol, Vec<Span>, Span)>,
    ) {
        if let Expr::Apply { callee, args, span, .. } = expr
            && let Expr::Var { name, .. } = callee.as_ref()
            && constrained_fn_names.contains(name)
            && name != self_name
            // FIXME 0653 — skip a §4.6 LOCAL shadow of a top-level constrained fn.
            && callee_has_keyed_carrier(var_refs, callee.span())
        {
            let arg_spans: Vec<Span> = args.iter().map(|a| a.span()).collect();
            out.push((name.clone(), arg_spans, *span));
        }
        for_each_child_expr(expr, |child| {
            Self::collect_constrained_calls_excluding_self(
                child, self_name, constrained_fn_names, var_refs, out,
            )
        });
    }

    // --- Result building ---


    /// Drain pending auto-curry resolutions into method_resolutions.
    ///
    /// Each entry in `pending_auto_curry` records a call site where the
    /// typechecker detected partial application (fewer args than params).
    /// This converts them to `ResolvedCall::AutoCurry` entries that the
    /// backend can use for codegen.
    ///
    /// `drain` selects the S115 settlement discipline (see
    /// [`AutoCurryDrain`]). Callers that run at a PRE-settlement seam (the
    /// per-form / per-variant body drains) pass [`AutoCurryDrain::Deferrable`];
    /// every recheck-scoped or settled seam passes [`AutoCurryDrain::Final`].
    pub(crate) fn resolve_auto_curry(&self, state: &mut CheckState) {
        self.resolve_auto_curry_with(state, AutoCurryDrain::Final)
    }

    /// [`Self::resolve_auto_curry`] with an explicit settlement discipline.
    pub(crate) fn resolve_auto_curry_with(&self, state: &mut CheckState, drain: AutoCurryDrain) {
        let pending = std::mem::take(&mut state.pending_auto_curry);
        for (span, name, applied_count, total_count, callee_ty, mut trait_resolution, callee_var_span)
            in pending
        {
            // If the trait resolution wasn't determined earlier (types were
            // still unresolved vars during try_auto_curry), attempt it now.
            // Later unifications (e.g., from a call site like `(make-adder 10)`)
            // may have pinned the type vars to concrete types.
            //
            // §11.8.8 (W3-review Important-1) — "the carrier is the IDENTITY". Gate
            // this raw-name re-resolution on the callee's recorded CARRIER VERDICT:
            // a callee resolved to a §4.6 LOCAL shadow (`(let [+ (fn [a b] 0)]
            // ((+ 1) 2))`) has `VarRef::Local`, so it must curry the LOCAL closure,
            // NOT re-derive the trait/primitive dispatch by raw name (mis-dispatch
            // → 3). `callee_has_keyed_carrier` is the shared P7 carrier guard (TRUE
            // only for `VarRef::Global`); a `None` inner resolution then transports
            // the local carrier downstream (below), currying the closure.
            if trait_resolution.is_none()
                && callee_var_span.is_none_or(|sp| {
                    callee_has_keyed_carrier(&state.method_resolutions.var_refs, sp)
                })
            {
                let resolved_callee = self.apply_subst(state, &callee_ty);
                if let Type::Fn(full_params, _) = &resolved_callee {
                    let resolved_params: Vec<Type> = full_params
                        .iter()
                        .map(|t| self.apply_subst(state, t))
                        .collect();
                    if let Ok(Some(r)) = self.try_resolve_trait_method(state, &name, &resolved_params, span) {
                        trait_resolution = Some(r);
                    } else if let Some(jit_name) = self.resolve_primitive_jit_name(state, &name) {
                        trait_resolution = Some(ResolvedCall::BuiltinFn { name: jit_name });
                    }
                }
            }

            // S115 W4 — the fn-as-value `'='` producer boundary
            // (`design/backend/s115-carrier-and-rc-sweep.md` §1.3). A trait
            // OPERATOR whose operand type is still a free `Var` at this seam
            // resolves to NO impl, so the transport branch below would carry the
            // callee `Var`'s `VarRef::Global(prelude/=)` — the trait-method
            // DECLARATION FQ, a dispatch-table key with no GOT slot — into
            // `ApplyRef::Dispatch`. The wrapper emitter then dies at the
            // GOT terminal ("reached codegen with no GOT-slot carrier").
            //
            // BOUNDARY (structural, both drains): a trait-method-decl FQ is
            // NEVER transported as a dispatch carrier. At a DEFERRABLE
            // (pre-settlement) seam the whole entry is held back for the
            // settled finalize drain, where the call site has pinned the
            // operand concrete and `try_resolve_trait_method` above yields the
            // real impl (`primitives/eq-i64`) — P26, record from settled state.
            if trait_resolution.is_none()
                && let Some(cvs) = callee_var_span
                && let Some(cranelisp_types::VarRef::Global(fq)) =
                    state.method_resolutions.var_refs.get(&cvs)
                && self.fq_is_trait_method_decl(fq)
            {
                if matches!(drain, AutoCurryDrain::Deferrable) {
                    state.deferred_auto_curry.push((
                        span,
                        name,
                        applied_count,
                        total_count,
                        callee_ty,
                        trait_resolution,
                        callee_var_span,
                    ));
                    continue;
                }
                // FINAL drain and still unresolved: record the `AutoCurry`
                // without a dispatch carrier (the Apply epilogue's
                // `ApplyRef::ViaCallee` stands). The backend's 0705 totality
                // table then reports a LOCATED producer contradiction rather
                // than the raw GOT-terminal miss — a decl FQ still never rides.
                state.method_resolutions.resolved_calls.insert(
                    span,
                    ResolvedCall::AutoCurry {
                        target_name: name,
                        applied_count,
                        total_count,
                        trait_resolution: None,
                    },
                );
                continue;
            }

            let has_inner = trait_resolution.is_some();
            let resolution = ResolvedCall::AutoCurry {
                target_name: name,
                applied_count,
                total_count,
                trait_resolution: trait_resolution.map(Box::new),
            };
            // S110 0583 leg 1 + W0.1b (§1.1.1): auto-curry carrier at the Apply
            // span. A trait/primitive curry derives from the inner resolution
            // (TraitMethod now reads `impl_module`). A PLAIN-fn curry instead
            // TRANSPORTS the callee `Var`'s already-recorded storage carrier
            // (resolve-once, shadow-correct) — the old `{current_module,
            // target}` derivation was wrong for an imported target. Matches
            // nothing for a local-binding target (`infer_var` records
            // `VarRef::Local`, not a `Global` — S114 carrier flip; was "recorded
            // nothing").
            if has_inner {
                self.record_dispatch_target(state, span, &resolution);
            } else if let Some(cvs) = callee_var_span
                && let Some(cranelisp_types::VarRef::Global(fq)) =
                    state.method_resolutions.var_refs.get(&cvs).cloned()
            {
                // A PLAIN-fn auto-curry over a TABLE-resolved callee (`Global`)
                // transports the callee's storage FQ as the Apply-span dispatch
                // carrier (S114 carrier flip). A curry over a LOCAL callee
                // (`VarRef::Local`) matches nothing here → the Apply epilogue's
                // `ApplyRef::ViaCallee` stands (the identity rides the callee).
                state
                    .method_resolutions
                    .apply_refs
                    .insert(span, cranelisp_types::ApplyRef::Dispatch(fq));
            }
            state.method_resolutions.resolved_calls.insert(span, resolution);
        }
    }


    /// Is `fq` the storage identity of a trait-method **DECLARATION** (the
    /// `deftrait` method entry carrying `trait_origin`), as opposed to a
    /// callable — a plain user fn, a builtin, or a resolved impl method?
    ///
    /// Carrier-keyed (Principle 24): the question is asked of the FQ that would
    /// be transported, not of the raw source name. A declaration entry is a
    /// dispatch-table key — it never has a GOT slot — so it must never appear in
    /// an `ApplyRef::Dispatch`.
    pub(crate) fn fq_is_trait_method_decl(&self, fq: &cranelisp_types::FQSymbol) -> bool {
        self.method_to_trait_in_module(&fq.module, &fq.symbol).is_some()
    }

    /// Resolve all recorded expr_types through the current substitution.
    pub(super) fn resolve_expr_types(&self, state: &CheckState) -> HashMap<Span, Type> {
        state.expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&state.subst, ty)))
            .collect()
    }

}

#[cfg(test)]
mod tests;
