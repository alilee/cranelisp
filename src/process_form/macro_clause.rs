//! Macro-clause compiler (S87 §1.1 extraction from `process_form.rs`).
//!
//! The SINGLE clause-compiler implementation (`compile_macro_clause_core`),
//! taking a [`MacroClauseEnv`] of the threaded references. Both callers build
//! the env from their own sources: the resolver path (`compile_macro_with_state`
//! in `macro_resolution.rs`, raw refs + shared-state→aliases derivation) and the
//! `_inline` adapter (the `&mut ModuleCompiler` Pass-2 path, also in
//! `macro_resolution.rs`, sourcing from `ctx`). This module is the **codegen**
//! of a clause
//! (synthesize → expand-qq → build → check → `inline_jit_codegen_for_names`),
//! distinct from `macro_resolution`'s *recognize/drive* concern
//! (`src/CLAUDE.md §"Macro-clause single implementation"`).

use cranelisp_types::{
    CranelispError, ErrorLocation, ModuleEntry, ModuleFullPath, Span, Symbol, TopLevel,
};

use crate::worker::build_program_compat;

/// The session/table + resolution environment threaded through on-demand
/// macro-clause compilation. Groups the cohesive reference set (module symbol
/// tables, the module-alias + prelude-fallback resolution scope, the per-module
/// typecheck products, and the optional live session) so the clause compiler
/// stays under the 8-param cap (Principle 6 — complexity has a budget). Each
/// entry shape (`compile_macro_clause_inline` from `&mut ModuleCompiler`, the
/// resolver's `compile_macro_with_state` from raw refs) builds the env from its
/// own reference sources; the values threaded are unchanged from the former
/// flat parameter lists.
pub(super) struct MacroClauseEnv<'a> {
    pub symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    pub module_aliases: &'a cranelisp_types::ModuleAliases,
    pub prelude_fallback: &'a cranelisp_typecheck::PreludeFallback,
    pub typecheck_products:
        &'a dashmap::DashMap<ModuleFullPath, crate::session_v4::TypecheckProduct>,
    pub shared_state: Option<&'a crate::session_v4::SharedState>,
}

/// Compile a single macro clause — the SINGLE implementation shared by both
/// entry shapes (FIXME 0109 Wave D collapse).
///
/// Post-Decision-44 the resolver path (`compile_macro_with_state`, raw refs)
/// and the `_inline` (`&mut ModuleCompiler`, Pass-2) clause compilers had
/// byte-identical bodies — the only difference was where the references came
/// from. This core takes them as a [`MacroClauseEnv`]; each caller builds the
/// env from its own reference sources. No behavioural change: each passes
/// exactly the references its former body used (the resolver path's
/// shared-state→aliases/prelude resolution, incl. the unit-test leaked-default
/// fallback, lives in the caller, unchanged).
pub(super) fn compile_macro_clause_core(
    env: &MacroClauseEnv<'_>,
    target_module: &ModuleFullPath,
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
) -> Result<(), CranelispError> {
    // Step 1: Synthesize the defn Sexp.
    let synth_sexp = cranelisp_frontend::synthesize_macro_clause_defn(
        macro_name.as_ref(),
        clause_idx,
        clause,
        span,
    );

    // Step 2: Expand quasiquotes.
    let expanded_sexp = cranelisp_frontend::expand_quasiquotes(&synth_sexp)?;

    // Step 3: Build AST. Macro clause synthesis emits compiler-generated
    // bodies whose Sexp tree comes from `synthesize_macro_clause_defn`; user
    // `(trace ...)` cannot reach this synthesis path. `InMemoryAndObject`
    // bypasses the validator.
    let program = build_program_compat(&[expanded_sexp])?;

    // Step 5: Extract the defn from the annotated symbol table (not the unannotated program).
    // The typechecker stores annotated defns (with resolved_call on AST nodes) in
    // ModuleEntry::Def.ast. Using the unannotated program would lose these annotations.
    let defn_name = program
        .iter()
        .find_map(|tl| match tl {
            TopLevel::Defn(d) => Some(d.name.clone()),
            _ => None,
        })
        .ok_or_else(|| CranelispError::MacroError {
            message: format!(
                "macro clause {} for '{}' produced no defn",
                clause_idx, macro_name
            ),
            location: ErrorLocation::from_span(span),
        })?;

    // Compile macro clause through the unified compile_to_module path.
    // Macro clause functions are normal functions on per-module GOTs — the
    // typechecker has registered `defn_name` on `target_module`'s symbol
    // table with `ast: Some(_)` and `got_slot: Some(_)` (Wave 0 invariant).
    // S69 Submission 35: `ModuleEntry::Def.ast` is now `DefnVariant` (no
    // `name` field); the codegen `names` array is keyed off the already-
    // extracted `defn_name`, so the prior `Defn` reconstruction is dropped.
    let mut turn = prepare_macro_clause_turn(env, target_module, &program, &defn_name, span)?;
    for batch_index in 0..turn.batches.len() {
        if let Err(error) = turn.compile_batch(batch_index) {
            turn.clear_reserved_slots();
            return Err(error);
        }
    }
    turn.publish(env);

    Ok(())
}

struct PreparedMacroTurn {
    settled: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    batches: Vec<(ModuleFullPath, Vec<Symbol>)>,
    final_cursors: std::collections::HashMap<ModuleFullPath, usize>,
    reserved: Vec<(ModuleFullPath, usize)>,
    live_leases: Vec<crate::code::Code>,
    typecheck_product: Option<(ModuleFullPath, crate::session_v4::TypecheckProduct)>,
    compiled_drop_glues: Vec<(
        ModuleFullPath,
        cranelisp_types::ConcreteType,
        cranelisp_backend::DropGlueArtifact,
        crate::code::Code,
    )>,
}

impl PreparedMacroTurn {
    fn compile_batch(&mut self, batch_index: usize) -> Result<(), CranelispError> {
        let (module, names) = &self.batches[batch_index];
        let mut jit = crate::worker::build_session_jit(&self.settled)?;
        let artifacts = cranelisp_backend::compile_to_module(
            module.clone(),
            names,
            &self.settled,
            jit.jit_module(),
            false,
        )?;
        #[allow(clippy::arc_with_non_send_sync)]
        let jit = std::sync::Arc::new(jit);
        let owner = crate::code::Code::jit(std::sync::Arc::clone(&jit));

        // The complete member set and callable shapes were validated during
        // preparation. After the backend's GOT commit this tail is therefore
        // ownership-only and infallible.
        let mut table = self
            .settled
            .get_mut(module)
            .unwrap_or_else(|| unreachable!("prepared macro module survives backend commit"));
        for name in names {
            let entry = table
                .symbols
                .get_mut(name)
                .unwrap_or_else(|| unreachable!("prepared macro member survives backend commit"));
            let ModuleEntry::Def { code, .. } = entry else {
                unreachable!("prepared macro member remains a definition")
            };
            *code = Some(owner.clone());
        }
        drop(table);
        self.compiled_drop_glues.extend(
            artifacts
                .drop_glues
                .into_iter()
                .map(|(ty, artifact)| (module.clone(), ty, artifact, owner.clone())),
        );
        Ok(())
    }

    fn clear_reserved_slots(&self) {
        for (module, slot) in &self.reserved {
            if let Some(table) = self.settled.get(module) {
                table.got.store_slot(*slot, std::ptr::null());
            }
        }
    }

    fn publish(mut self, env: &MacroClauseEnv<'_>) {
        let _live_leases = &self.live_leases;

        // Candidate entries already own their JITs. Install generated-glue
        // owners and displaced-code owners in their session homes before
        // moving any entry that makes a reserved pointer reachable.
        if let Some(shared) = env.shared_state {
            for (module, ty, artifact, owner) in self.compiled_drop_glues.drain(..) {
                shared.fresh_jit_drop_glues.insert(
                    (module, ty),
                    crate::worker::FreshJitDropGlue { artifact, owner },
                );
            }
            let mut retained = shared
                .retained_code
                .lock()
                .unwrap_or_else(|error| error.into_inner());
            for (module, names) in &self.batches {
                let live = env
                    .symbol_tables
                    .get(module)
                    .unwrap_or_else(|| unreachable!("live macro module survives cadence"));
                for name in names {
                    if let Some(ModuleEntry::Def {
                        code: Some(owner), ..
                    }) = live.symbols.get(name)
                    {
                        retained.push(crate::redefine::RetainedCode::frozen(
                            module,
                            name,
                            live.symbols
                                .get(name)
                                .and_then(ModuleEntry::callable_got_slot),
                            owner.clone(),
                        ));
                    }
                }
            }
        }

        for (module, names) in &self.batches {
            let mut settled = self
                .settled
                .get_mut(module)
                .unwrap_or_else(|| unreachable!("prepared macro module survives publish"));
            let mut live = env
                .symbol_tables
                .get_mut(module)
                .unwrap_or_else(|| unreachable!("live macro module survives cadence"));
            if let Some(cursor) = self.final_cursors.remove(module) {
                live.next_got_slot = cursor;
            }
            for name in names {
                let entry = settled
                    .symbols
                    .remove(name)
                    .unwrap_or_else(|| unreachable!("prepared macro member survives publish"));
                live.symbols.insert(name.clone(), entry);
            }
        }
        if let Some((module, product)) = self.typecheck_product.take() {
            env.typecheck_products.insert(module, product);
        }
    }
}

struct TurnCheckWorld {
    baseline: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    settled: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
}

impl TurnCheckWorld {
    fn from_baseline(
        baseline: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    ) -> Self {
        Self {
            settled: baseline.clone(),
            baseline,
        }
    }
}

#[derive(Default)]
struct TurnDelta {
    entries: std::collections::HashMap<cranelisp_types::FQSymbol, ModuleEntry<crate::code::Code>>,
}

#[derive(Default)]
struct FqWorklist {
    pending: Vec<cranelisp_types::FQSymbol>,
    queued: std::collections::HashSet<cranelisp_types::FQSymbol>,
}

impl FqWorklist {
    fn enqueue(&mut self, fq: cranelisp_types::FQSymbol) {
        if self.queued.insert(fq.clone()) {
            self.pending.push(fq);
        }
    }
}

fn collect_codegen_dependencies(
    variant: &cranelisp_types::MonoDefnVariant,
    worklist: &mut FqWorklist,
) {
    use cranelisp_types::{ApplyRef, MonoExpr, VarRef};

    fn walk(expr: &MonoExpr, worklist: &mut FqWorklist) {
        match expr {
            MonoExpr::IntLit { .. }
            | MonoExpr::FloatLit { .. }
            | MonoExpr::BoolLit { .. }
            | MonoExpr::StringLit { .. } => {}
            MonoExpr::Var { resolution, .. } => {
                if let VarRef::Global(fq) = resolution {
                    worklist.enqueue(fq.clone());
                }
            }
            MonoExpr::Let { bindings, body, .. } | MonoExpr::ParBind { bindings, body, .. } => {
                for (_, value) in bindings {
                    walk(value, worklist);
                }
                walk(body, worklist);
            }
            MonoExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                walk(cond, worklist);
                walk(then_branch, worklist);
                walk(else_branch, worklist);
            }
            MonoExpr::Lambda { body, .. } | MonoExpr::Trace { body, .. } => {
                walk(body, worklist);
            }
            MonoExpr::Apply {
                callee,
                args,
                dispatch,
                ..
            } => {
                match dispatch {
                    ApplyRef::Dispatch(fq) => worklist.enqueue(fq.clone()),
                    ApplyRef::ViaCallee => walk(callee, worklist),
                }
                for arg in args {
                    walk(arg, worklist);
                }
            }
            MonoExpr::Match {
                scrutinee, arms, ..
            } => {
                walk(scrutinee, worklist);
                for arm in arms {
                    walk(&arm.body, worklist);
                }
            }
            MonoExpr::VecLit { elements, .. } => {
                for element in elements {
                    walk(element, worklist);
                }
            }
            MonoExpr::LaunchContinue {
                launched,
                continuation,
                ..
            } => {
                walk(launched, worklist);
                walk(continuation, worklist);
            }
            MonoExpr::ConstrADT { fields, .. } => {
                for field in fields {
                    walk(field, worklist);
                }
            }
        }
    }

    walk(&variant.body, worklist);
}

fn clone_table_world(
    tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
) -> dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
    let world = dashmap::DashMap::new();
    for table in tables.iter() {
        world.insert(table.key().clone(), table.value().clone());
    }
    world
}

fn entry_fingerprint(entry: &ModuleEntry<crate::code::Code>) -> String {
    let mut semantic = entry.clone();
    if let ModuleEntry::Def { code, .. } = &mut semantic {
        *code = None;
    }
    format!("{semantic:?}")
}

fn baseline_entry_is_executable(
    table: &crate::code::SessionSymbolTable,
    entry: &ModuleEntry<crate::code::Code>,
) -> bool {
    let backend_leaf = matches!(
        entry,
        ModuleEntry::Def { kind, .. }
            if matches!(
                kind.as_ref(),
                cranelisp_types::DefKind::Constructor { .. }
                    | cranelisp_types::DefKind::PrimitiveExtern
                    | cranelisp_types::DefKind::Primitive {
                        body: cranelisp_types::PrimitiveBody::Inline,
                        ..
                    }
            )
    );
    backend_leaf
        || (entry.is_callable_target()
            && entry
                .callable_got_slot()
                .is_some_and(|slot| !table.got.load_slot(slot).is_null()))
}

fn enroll_non_executable_seed(
    baseline: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    delta: &mut TurnDelta,
    seed: &cranelisp_types::FQSymbol,
    fresh_candidate: Option<&ModuleEntry<crate::code::Code>>,
    span: Span,
) -> Result<(), CranelispError> {
    if delta.entries.contains_key(seed) {
        return Ok(());
    }
    if baseline.get(&seed.module).is_some_and(|table| {
        table
            .get(seed.symbol.as_ref())
            .is_some_and(|entry| baseline_entry_is_executable(&table, entry))
    }) {
        return Ok(());
    }
    let candidate = fresh_candidate.ok_or_else(|| CranelispError::MacroError {
        message: format!(
            "fresh macro seed '{}/{}' is missing",
            seed.module, seed.symbol
        ),
        location: ErrorLocation::from_span(span),
    })?;
    let settled_callable = candidate.callable_got_slot().is_some()
        && matches!(
            candidate,
            ModuleEntry::Def {
                codegen_view: Some(_),
                ..
            }
        );
    if !settled_callable {
        return Err(CranelispError::MacroError {
            message: format!(
                "fresh macro seed '{}/{}' is not a concrete callable with a settled codegen view",
                seed.module, seed.symbol
            ),
            location: ErrorLocation::from_span(span),
        });
    }
    delta.entries.insert(seed.clone(), candidate.clone());
    Ok(())
}

fn set_callable_slot(entry: &mut ModuleEntry<crate::code::Code>, slot: usize) {
    use cranelisp_types::{DefKind, PrimitiveBody, UserFnState};
    let ModuleEntry::Def { kind, .. } = entry else {
        return;
    };
    match kind.as_mut() {
        DefKind::UserFn {
            fn_state:
                UserFnState::Concrete {
                    got_slot,
                    mode_summary: _,
                },
        } => *got_slot = slot,
        DefKind::Constructor { got_slot, .. } | DefKind::PlatformEffect { got_slot, .. } => {
            *got_slot = slot
        }
        DefKind::Primitive {
            body: PrimitiveBody::Extern { got_slot, .. },
            ..
        } => *got_slot = slot,
        _ => {}
    }
}

fn prepare_macro_clause_turn(
    env: &MacroClauseEnv<'_>,
    target_module: &ModuleFullPath,
    program: &[TopLevel],
    clause_name: &Symbol,
    span: Span,
) -> Result<PreparedMacroTurn, CranelispError> {
    use cranelisp_typecheck::{CheckError, SymbolTableAccess, check_forms};

    let baseline = clone_table_world(env.symbol_tables);
    let world = TurnCheckWorld::from_baseline(baseline);
    let typecheck_product = env
        .typecheck_products
        .get(target_module)
        .map(|product| crate::session_v4::TypecheckProduct {
            file_path: product.file_path.clone(),
            source_text: product.source_text.clone(),
            unresolved_dispatch: product.unresolved_dispatch.clone(),
        })
        .unwrap_or_else(|| crate::session_v4::TypecheckProduct {
            file_path: None,
            source_text: None,
            unresolved_dispatch: Vec::new(),
        });
    let mut staging = crate::code::SessionSymbolTable::new_with_params(target_module.clone());
    let parsed = crate::worker::top_level_to_parsed_entries(program);
    let mut access =
        SymbolTableAccess::cluster(&world.settled, &mut staging, target_module.clone());
    match check_forms(
        parsed,
        &mut access,
        &world.settled,
        env.module_aliases,
        env.prelude_fallback,
    ) {
        Ok(_) => {}
        Err(CheckError::Gap(gap)) => {
            return Err(CranelispError::TypeError {
                message: format!("unresolved cross-module reference: {gap:?}"),
                location: ErrorLocation::from_span(span),
            });
        }
        Err(error) => return Err(crate::worker::check_error_to_cranelisp_error(error)),
    }
    drop(access);

    let seed = cranelisp_types::FQSymbol {
        module: target_module.clone(),
        symbol: clause_name.clone(),
    };
    let fresh_seed = staging.get(clause_name.as_ref()).cloned();

    // Overlay the target staging into the owned settled world. Slot assignment
    // is deferred until the exact keyed closure is known.
    {
        let mut target =
            world
                .settled
                .get_mut(target_module)
                .ok_or_else(|| CranelispError::MacroError {
                    message: format!("macro module '{target_module}' disappeared from turn world"),
                    location: ErrorLocation::from_span(span),
                })?;
        for (name, entry) in staging.symbols {
            target.symbols.insert(name, entry);
        }
    }

    let mut delta = TurnDelta::default();
    for table in world.settled.iter() {
        let module = table.key().clone();
        for (name, entry) in table.all_symbols() {
            let changed = world
                .baseline
                .get(&module)
                .and_then(|base| base.get(name.as_ref()).cloned())
                .is_none_or(|prior| entry_fingerprint(&prior) != entry_fingerprint(entry));
            if changed {
                delta.entries.insert(
                    cranelisp_types::FQSymbol {
                        module: module.clone(),
                        symbol: name.clone(),
                    },
                    entry.clone(),
                );
            }
        }
    }

    enroll_non_executable_seed(
        &world.baseline,
        &mut delta,
        &seed,
        fresh_seed.as_ref(),
        span,
    )?;
    let (closure, live_leases) =
        derive_macro_turn_closure(&world.baseline, &mut delta, seed, span)?;

    // `closure` is dependency-first postorder. Preserve that module order;
    // alphabetic grouping would compile a caller before its dependency.
    let mut by_module: Vec<(ModuleFullPath, Vec<Symbol>)> = Vec::new();
    for fq in closure {
        if delta.entries.contains_key(&fq) {
            if let Some((_, names)) = by_module
                .iter_mut()
                .find(|(module, _)| *module == fq.module)
            {
                names.push(fq.symbol);
            } else {
                by_module.push((fq.module, vec![fq.symbol]));
            }
        }
    }
    let mut final_cursors = std::collections::HashMap::new();
    let mut reserved = Vec::new();
    for (module, names) in &mut by_module {
        names.sort();
        names.dedup();
        let mut table =
            world
                .settled
                .get_mut(module)
                .ok_or_else(|| CranelispError::MacroError {
                    message: format!("macro dependency module '{module}' disappeared"),
                    location: ErrorLocation::from_span(span),
                })?;
        let mut cursor = world
            .baseline
            .get(module)
            .map_or(0, |base| base.next_got_slot);
        for name in names.iter() {
            let entry = table
                .symbols
                .get_mut(name)
                .ok_or_else(|| CranelispError::MacroError {
                    message: format!("macro dependency '{module}/{name}' disappeared"),
                    location: ErrorLocation::from_span(span),
                })?;
            if entry.callable_got_slot().is_some() {
                if cursor >= cranelisp_types::GOT_TABLE_SIZE {
                    return Err(CranelispError::MacroError {
                        message: format!("macro dependency module '{module}' exhausted its GOT"),
                        location: ErrorLocation::from_span(span),
                    });
                }
                set_callable_slot(entry, cursor);
                reserved.push((module.clone(), cursor));
                cursor += 1;
            }
        }
        final_cursors.insert(module.clone(), cursor);
    }
    Ok(PreparedMacroTurn {
        settled: world.settled,
        batches: by_module,
        final_cursors,
        reserved,
        live_leases,
        typecheck_product: Some((target_module.clone(), typecheck_product)),
        compiled_drop_glues: Vec::new(),
    })
}

fn derive_macro_turn_closure(
    baseline: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    delta: &mut TurnDelta,
    seed: cranelisp_types::FQSymbol,
    span: Span,
) -> Result<(Vec<cranelisp_types::FQSymbol>, Vec<crate::code::Code>), CranelispError> {
    fn visit(
        fq: cranelisp_types::FQSymbol,
        baseline: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        delta: &mut TurnDelta,
        visiting: &mut std::collections::HashSet<cranelisp_types::FQSymbol>,
        visited: &mut std::collections::HashSet<cranelisp_types::FQSymbol>,
        ordered: &mut Vec<cranelisp_types::FQSymbol>,
        live_leases: &mut Vec<crate::code::Code>,
        span: Span,
    ) -> Result<(), CranelispError> {
        if visited.contains(&fq) || !visiting.insert(fq.clone()) {
            return Ok(());
        }
        if let Some(entry) = delta.entries.get(&fq).cloned() {
            let is_concrete_callable = entry.callable_got_slot().is_some();
            let view = match &entry {
                ModuleEntry::Def {
                    codegen_view: Some(view),
                    ..
                } if is_concrete_callable => view.clone(),
                _ => {
                    return Err(CranelispError::MacroError {
                        message: format!(
                            "selected macro dependency '{}/{}' is not a concrete callable \
                             with a settled codegen view",
                            fq.module, fq.symbol
                        ),
                        location: ErrorLocation::from_span(span),
                    });
                }
            };
            let mut dependencies = FqWorklist::default();
            collect_codegen_dependencies(&view, &mut dependencies);
            dependencies.pending.sort_by(|a, b| {
                (a.module.as_ref(), a.symbol.as_ref()).cmp(&(b.module.as_ref(), b.symbol.as_ref()))
            });
            for callee in dependencies.pending {
                visit(
                    callee,
                    baseline,
                    delta,
                    visiting,
                    visited,
                    ordered,
                    live_leases,
                    span,
                )?;
            }
            visiting.remove(&fq);
            visited.insert(fq.clone());
            ordered.push(fq);
            return Ok(());
        }
        let entry = baseline
            .get(&fq.module)
            .and_then(|table| table.get(fq.symbol.as_ref()).cloned())
            .ok_or_else(|| CranelispError::MacroError {
                message: format!("macro dependency '{}/{}' is missing", fq.module, fq.symbol),
                location: ErrorLocation::from_span(span),
            })?;
        let executable = baseline
            .get(&fq.module)
            .is_some_and(|table| baseline_entry_is_executable(&table, &entry));
        if !executable {
            return Err(CranelispError::MacroError {
                message: format!(
                    "selected baseline macro dependency '{}/{}' is not executable",
                    fq.module, fq.symbol
                ),
                location: ErrorLocation::from_span(span),
            });
        }
        if let ModuleEntry::Def {
            code: Some(owner), ..
        } = &entry
        {
            live_leases.push(owner.clone());
        }
        visiting.remove(&fq);
        visited.insert(fq);
        Ok(())
    }

    let mut visiting = std::collections::HashSet::new();
    let mut visited = std::collections::HashSet::new();
    let mut ordered = Vec::new();
    let mut live_leases = Vec::new();
    visit(
        seed,
        baseline,
        delta,
        &mut visiting,
        &mut visited,
        &mut ordered,
        &mut live_leases,
        span,
    )?;
    Ok((ordered, live_leases))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fq(module: &str, symbol: &str) -> cranelisp_types::FQSymbol {
        cranelisp_types::FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(symbol),
        }
    }

    fn concrete_callable(
        name: &str,
        value: i64,
        with_view: bool,
    ) -> ModuleEntry<crate::code::Code> {
        use cranelisp_types::{
            ConcreteType, DefKind, MonoDefnVariant, MonoExpr, Scheme, Type, UserFnState,
        };

        let mut entry = ModuleEntry::def(
            Scheme {
                type_vars: Vec::new(),
                constraints: std::collections::HashMap::new(),
                ty: Type::Fn(Vec::new(), Box::new(Type::Int)),
            },
            DefKind::UserFn {
                fn_state: UserFnState::Concrete {
                    got_slot: 0,
                    mode_summary: None,
                },
            },
        )
        .build();
        if with_view {
            let ModuleEntry::Def { codegen_view, .. } = &mut entry else {
                unreachable!("builder produced a definition")
            };
            *codegen_view = Some(MonoDefnVariant {
                name: Symbol::from(name),
                params: Vec::new(),
                body: MonoExpr::IntLit {
                    value,
                    span: Span::SYNTHETIC,
                    ty: ConcreteType::Int,
                },
                span: Span::SYNTHETIC,
                mode_summary: None,
            });
        }
        entry
    }

    fn nonconcrete_callable() -> ModuleEntry<crate::code::Code> {
        use cranelisp_types::{DefKind, Scheme, Type, UserFnState};

        ModuleEntry::def(
            Scheme {
                type_vars: Vec::new(),
                constraints: std::collections::HashMap::new(),
                ty: Type::Fn(Vec::new(), Box::new(Type::Int)),
            },
            DefKind::UserFn {
                fn_state: UserFnState::NotDetermined,
            },
        )
        .build()
    }

    fn baseline_with(
        module: &ModuleFullPath,
        name: &Symbol,
        entry: ModuleEntry<crate::code::Code>,
    ) -> dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
        let baseline = dashmap::DashMap::new();
        let mut table = crate::code::SessionSymbolTable::new_with_params(module.clone());
        table.insert(name.clone(), entry);
        baseline.insert(module.clone(), table);
        baseline
    }

    #[test]
    fn non_executable_equal_seed_enrolls_only_fresh_concrete_candidate() {
        let seed = fq("cached.macros", "clause");
        let baseline_entry = concrete_callable(seed.symbol.as_ref(), 42, true);
        let baseline = baseline_with(&seed.module, &seed.symbol, baseline_entry.clone());
        let candidate = baseline_entry;
        let mut delta = TurnDelta::default();

        enroll_non_executable_seed(
            &baseline,
            &mut delta,
            &seed,
            Some(&candidate),
            Span::SYNTHETIC,
        )
        .expect("fresh settled seed replaces missing executable carriers");

        assert_eq!(delta.entries.len(), 1);
        assert_eq!(
            delta.entries.get(&seed).map(entry_fingerprint),
            Some(entry_fingerprint(&candidate))
        );
        assert!(
            baseline
                .get(&seed.module)
                .unwrap()
                .got
                .load_slot(0)
                .is_null(),
            "classification never mutates the restored baseline GOT"
        );
    }

    #[test]
    fn executable_equal_seed_remains_baseline_dependency() {
        use cranelisp_backend::cache::linker::Linker;
        use std::sync::Arc;

        let seed = fq("live.macros", "clause");
        let mut baseline_entry = concrete_callable(seed.symbol.as_ref(), 42, true);
        let ModuleEntry::Def { code, .. } = &mut baseline_entry else {
            unreachable!("callable helper builds a definition")
        };
        *code = Some(crate::code::Code::linker(Arc::new(
            Linker::new().expect("test linker"),
        )));
        let baseline = baseline_with(&seed.module, &seed.symbol, baseline_entry.clone());
        baseline
            .get(&seed.module)
            .unwrap()
            .got
            .store_slot(0, std::ptr::dangling_mut::<u8>());
        let mut delta = TurnDelta::default();

        enroll_non_executable_seed(
            &baseline,
            &mut delta,
            &seed,
            Some(&baseline_entry),
            Span::SYNTHETIC,
        )
        .expect("live baseline seed remains authoritative");

        assert!(delta.entries.is_empty(), "live seed is not recompiled");
        let (ordered, leases) =
            derive_macro_turn_closure(&baseline, &mut delta, seed, Span::SYNTHETIC)
                .expect("executable baseline seed closes as a leased dependency");
        assert!(ordered.is_empty());
        assert_eq!(leases.len(), 1, "baseline Code owner remains leased");
    }

    #[test]
    fn semantic_change_already_in_delta_is_not_replaced_or_duplicated() {
        let seed = fq("changed.macros", "clause");
        let baseline = baseline_with(
            &seed.module,
            &seed.symbol,
            concrete_callable(seed.symbol.as_ref(), 1, true),
        );
        let changed = concrete_callable(seed.symbol.as_ref(), 2, true);
        let ignored_candidate = concrete_callable(seed.symbol.as_ref(), 3, true);
        let mut delta = TurnDelta::default();
        delta.entries.insert(seed.clone(), changed.clone());

        enroll_non_executable_seed(
            &baseline,
            &mut delta,
            &seed,
            Some(&ignored_candidate),
            Span::SYNTHETIC,
        )
        .expect("ordinary semantic delta remains authoritative");

        assert_eq!(delta.entries.len(), 1);
        assert_eq!(
            delta.entries.get(&seed).map(entry_fingerprint),
            Some(entry_fingerprint(&changed))
        );
    }

    #[test]
    fn non_executable_seed_requires_present_concrete_settled_candidate() {
        let seed = fq("invalid.macros", "clause");
        let baseline = baseline_with(
            &seed.module,
            &seed.symbol,
            concrete_callable(seed.symbol.as_ref(), 42, true),
        );

        let absent = enroll_non_executable_seed(
            &baseline,
            &mut TurnDelta::default(),
            &seed,
            None,
            Span::SYNTHETIC,
        )
        .expect_err("missing fresh seed is a hard preparation error");
        assert!(absent.to_string().contains("fresh macro seed"));
        assert!(absent.to_string().contains("is missing"));

        let generic = nonconcrete_callable();
        let nonconcrete = enroll_non_executable_seed(
            &baseline,
            &mut TurnDelta::default(),
            &seed,
            Some(&generic),
            Span::SYNTHETIC,
        )
        .expect_err("generic fresh seed is rejected");
        assert!(nonconcrete.to_string().contains("not a concrete callable"));

        let no_view = concrete_callable(seed.symbol.as_ref(), 42, false);
        let unsettled = enroll_non_executable_seed(
            &baseline,
            &mut TurnDelta::default(),
            &seed,
            Some(&no_view),
            Span::SYNTHETIC,
        )
        .expect_err("fresh seed without codegen view is rejected");
        assert!(unsettled.to_string().contains("settled codegen view"));
    }

    #[test]
    fn unrelated_non_executable_baseline_row_is_never_promoted() {
        let seed = fq("cached.macros", "clause");
        let unrelated = fq("cached.macros", "other");
        let baseline = baseline_with(
            &seed.module,
            &seed.symbol,
            concrete_callable(seed.symbol.as_ref(), 42, true),
        );
        baseline.get_mut(&unrelated.module).unwrap().insert(
            unrelated.symbol.clone(),
            concrete_callable(unrelated.symbol.as_ref(), 7, true),
        );
        let candidate = concrete_callable(seed.symbol.as_ref(), 42, true);
        let mut delta = TurnDelta::default();

        enroll_non_executable_seed(
            &baseline,
            &mut delta,
            &seed,
            Some(&candidate),
            Span::SYNTHETIC,
        )
        .expect("seed-specific enrollment succeeds");

        assert!(delta.entries.contains_key(&seed));
        assert!(!delta.entries.contains_key(&unrelated));
    }

    fn prepared_product_turn(
        module: &ModuleFullPath,
        settled: dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        batches: Vec<(ModuleFullPath, Vec<Symbol>)>,
    ) -> PreparedMacroTurn {
        PreparedMacroTurn {
            settled,
            batches,
            final_cursors: std::collections::HashMap::new(),
            reserved: Vec::new(),
            live_leases: Vec::new(),
            typecheck_product: Some((
                module.clone(),
                crate::session_v4::TypecheckProduct {
                    file_path: None,
                    source_text: None,
                    unresolved_dispatch: Vec::new(),
                },
            )),
            compiled_drop_glues: Vec::new(),
        }
    }

    fn test_shared_state() -> crate::session_v4::SharedState {
        use std::sync::Mutex;
        use std::sync::atomic::{AtomicBool, AtomicU32};

        crate::session_v4::SharedState {
            scheduler: crate::scheduler::CompileScheduler::new(),
            project_root: std::path::PathBuf::new(),
            lib_dirs: Mutex::new(Vec::new()),
            platform_dirs: Mutex::new(Vec::new()),
            module_aliases: cranelisp_types::ModuleAliases::default(),
            prelude_fallback: cranelisp_typecheck::PreludeFallback::default(),
            declared_exports: crate::imports::DeclaredExports::default(),
            cache: std::sync::Arc::new(crate::cache::ObjectCache::new(None, None)),
            promote_nice_workers: AtomicBool::new(false),
            file_to_module: Mutex::new(std::collections::HashMap::new()),
            symbol_tables: dashmap::DashMap::new(),
            next_type_id: AtomicU32::new(0),
            typecheck_products: dashmap::DashMap::new(),
            kept_dlls: Mutex::new(Vec::new()),
            introspection: Some(dashmap::DashMap::new()),
            importable_indices: crate::session_v4::ImportableIndices::default(),
            broken: dashmap::DashMap::new(),
            retained_code: Mutex::new(Vec::new()),
            fresh_jit_drop_glues: dashmap::DashMap::new(),
            run_mode: crate::session_v4::RunMode::Repl,
            test_runner_state: Box::new(crate::session_v4::TestRunnerState::stub()),
        }
    }

    #[test]
    fn owned_baseline_never_observes_concurrent_concrete_specialization() {
        use cranelisp_types::{
            ApplyRef, ConcreteType, DefKind, MonoDefnVariant, MonoExpr, Scheme, Type, UserFnState,
        };

        fn concrete_entry(name: &str, body: MonoExpr) -> ModuleEntry<crate::code::Code> {
            let mut entry = ModuleEntry::def(
                Scheme {
                    type_vars: Vec::new(),
                    constraints: std::collections::HashMap::new(),
                    ty: Type::Fn(Vec::new(), Box::new(Type::Int)),
                },
                DefKind::UserFn {
                    fn_state: UserFnState::Concrete {
                        got_slot: 0,
                        mode_summary: None,
                    },
                },
            )
            .build();
            let ModuleEntry::Def { codegen_view, .. } = &mut entry else {
                unreachable!("builder produced a definition")
            };
            *codegen_view = Some(MonoDefnVariant {
                name: Symbol::from(name),
                params: Vec::new(),
                body,
                span: Span::SYNTHETIC,
                mode_summary: None,
            });
            entry
        }

        let module = ModuleFullPath::from("owned.world");
        let live = dashmap::DashMap::new();
        live.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let captured = clone_table_world(&live);

        let concurrent = fq("owned.world", "helper$Int");
        let concurrent_entry = concrete_entry(
            concurrent.symbol.as_ref(),
            MonoExpr::IntLit {
                value: 1,
                span: Span::SYNTHETIC,
                ty: ConcreteType::Int,
            },
        );
        live.get_mut(&module)
            .unwrap()
            .symbols
            .insert(concurrent.symbol.clone(), concurrent_entry);
        let live_fingerprint = live
            .get(&module)
            .and_then(|table| table.get(concurrent.symbol.as_ref()).map(entry_fingerprint))
            .expect("concurrent row is live");

        // The constructor has no live-table parameter: the already-owned
        // baseline is its entire observable world.
        let world = TurnCheckWorld::from_baseline(captured);
        assert!(
            world
                .settled
                .get(&module)
                .and_then(|table| table.get(concurrent.symbol.as_ref()).cloned())
                .is_none()
        );

        let seed = fq("owned.world", "clause");
        let target = concrete_entry(
            seed.symbol.as_ref(),
            MonoExpr::Apply {
                callee: Box::new(MonoExpr::IntLit {
                    value: 0,
                    span: Span::SYNTHETIC,
                    ty: ConcreteType::Int,
                }),
                args: Vec::new(),
                span: Span::SYNTHETIC,
                resolved_call: None,
                dispatch: ApplyRef::Dispatch(concurrent.clone()),
                ty: ConcreteType::Int,
                escapes: None,
                confined: None,
                unique_static: None,
                provenance: None,
            },
        );
        let mut delta = TurnDelta::default();
        delta.entries.insert(seed.clone(), target);

        let error = derive_macro_turn_closure(&world.baseline, &mut delta, seed, Span::SYNTHETIC)
            .expect_err("captured baseline must miss a later concurrent specialization");
        assert!(error.to_string().contains("helper$Int"));
        assert!(
            !delta.entries.contains_key(&concurrent),
            "concurrent live row is never classified into the owned TurnDelta or a compile batch"
        );
        assert_eq!(
            live.get(&module)
                .and_then(|table| table.get(concurrent.symbol.as_ref()).map(entry_fingerprint))
                .as_deref(),
            Some(live_fingerprint.as_str()),
            "keyed miss leaves the concurrently published live row untouched"
        );
    }

    #[test]
    fn composed_macro_turn_later_failure_rolls_back_every_product() {
        use cranelisp_typecheck::{SymbolTableAccess, check_forms};

        let shared = test_shared_state();
        let helper_module = ModuleFullPath::from("helper");
        let target_module = ModuleFullPath::from("macro.target");
        shared.symbol_tables.insert(
            helper_module.clone(),
            crate::code::SessionSymbolTable::new_with_params(helper_module.clone()),
        );
        shared.symbol_tables.insert(
            target_module.clone(),
            crate::code::SessionSymbolTable::new_with_params(target_module.clone()),
        );

        let helper_sexps =
            cranelisp_frontend::parse("(defn identity [x] x)").expect("helper parses");
        let helper_program = build_program_compat(&helper_sexps).expect("helper builds");
        let mut helper_staging =
            crate::code::SessionSymbolTable::new_with_params(helper_module.clone());
        let mut helper_access = SymbolTableAccess::cluster(
            &shared.symbol_tables,
            &mut helper_staging,
            helper_module.clone(),
        );
        check_forms(
            crate::worker::top_level_to_parsed_entries(&helper_program),
            &mut helper_access,
            &shared.symbol_tables,
            &shared.module_aliases,
            &shared.prelude_fallback,
        )
        .expect("polymorphic helper typechecks");
        drop(helper_access);
        {
            let mut live = shared.symbol_tables.get_mut(&helper_module).unwrap();
            for (name, entry) in helper_staging.symbols {
                live.symbols.insert(name, entry);
            }
        }
        shared
            .symbol_tables
            .get_mut(&target_module)
            .unwrap()
            .insert(
                Symbol::from("identity"),
                ModuleEntry::Import {
                    source: fq("helper", "identity"),
                    visibility: cranelisp_types::Visibility::Private,
                },
            );

        let target_sexps =
            cranelisp_frontend::parse("(defn clause [] (identity 1))").expect("target parses");
        let target_program = build_program_compat(&target_sexps).expect("target builds");
        let env = MacroClauseEnv {
            symbol_tables: &shared.symbol_tables,
            module_aliases: &shared.module_aliases,
            prelude_fallback: &shared.prelude_fallback,
            typecheck_products: &shared.typecheck_products,
            shared_state: Some(&shared),
        };
        let mut turn = prepare_macro_clause_turn(
            &env,
            &target_module,
            &target_program,
            &Symbol::from("clause"),
            Span::SYNTHETIC,
        )
        .expect("real macro preparation succeeds");
        let prepared_names = turn
            .batches
            .iter()
            .find(|(module, _)| module == &target_module)
            .map(|(_, names)| names.clone())
            .expect("target batch exists");
        let helper_specialization = prepared_names
            .iter()
            .find(|name| name.as_ref().contains("identity$"))
            .cloned()
            .expect("typecheck minted the concrete helper specialization");
        assert!(
            prepared_names.contains(&Symbol::from("clause")),
            "typed closure includes its target clause"
        );
        turn.batches = vec![
            (target_module.clone(), vec![helper_specialization.clone()]),
            (target_module.clone(), vec![Symbol::from("clause")]),
        ];
        let before_cursors: std::collections::HashMap<_, _> = [&helper_module, &target_module]
            .into_iter()
            .map(|module| {
                (
                    module.clone(),
                    shared.symbol_tables.get(module).unwrap().next_got_slot,
                )
            })
            .collect();
        let before_entries: std::collections::HashMap<_, _> = [&helper_module, &target_module]
            .into_iter()
            .map(|module| {
                let table = shared.symbol_tables.get(module).unwrap();
                let mut rows: Vec<_> = table
                    .all_symbols()
                    .map(|(name, entry)| (name.clone(), entry_fingerprint(entry)))
                    .collect();
                rows.sort();
                (module.clone(), rows)
            })
            .collect();
        let before_retention = shared.retained_code.lock().unwrap().len();
        assert!(shared.typecheck_products.get(&target_module).is_none());

        turn.compile_batch(0)
            .expect("earlier dependency batch compiles for real");
        assert!(
            turn.reserved.iter().any(|(module, slot)| {
                module == &target_module
                    && !shared
                        .symbol_tables
                        .get(module)
                        .unwrap()
                        .got
                        .load_slot(*slot)
                        .is_null()
            }),
            "earlier backend success writes a reserved canonical GOT cell"
        );
        let (later_module, later_names) = &turn.batches[1];
        {
            let mut table = turn.settled.get_mut(later_module).unwrap();
            let ModuleEntry::Def { codegen_view, .. } =
                table.symbols.get_mut(&later_names[0]).unwrap()
            else {
                panic!("later prepared member remains a definition")
            };
            *codegen_view = None;
        }
        assert!(
            turn.compile_batch(1).is_err(),
            "malformed later real batch forces backend failure"
        );
        turn.clear_reserved_slots();
        assert!(
            turn.reserved.iter().all(|(module, slot)| shared
                .symbol_tables
                .get(module)
                .unwrap()
                .got
                .load_slot(*slot)
                .is_null()),
            "every reserved canonical cell is cleared while earlier JIT owners remain held"
        );

        for module in [&helper_module, &target_module] {
            let table = shared.symbol_tables.get(module).unwrap();
            assert_eq!(
                table.next_got_slot, before_cursors[module],
                "{module} cursor"
            );
            let mut rows: Vec<_> = table
                .all_symbols()
                .map(|(name, entry)| (name.clone(), entry_fingerprint(entry)))
                .collect();
            rows.sort();
            assert_eq!(rows, before_entries[module], "{module} entries");
        }
        assert!(shared.typecheck_products.get(&target_module).is_none());
        assert_eq!(shared.retained_code.lock().unwrap().len(), before_retention);
        drop(turn);
    }

    #[test]
    fn macro_typecheck_product_publishes_only_after_backend_success() {
        use cranelisp_types::{DefKind, Scheme, Type, UserFnState};

        let module = ModuleFullPath::from("macros.product");
        let bad_name = Symbol::from("bad");
        let live = dashmap::DashMap::new();
        live.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let products = dashmap::DashMap::new();
        let aliases = cranelisp_types::ModuleAliases::default();
        let prelude = cranelisp_typecheck::PreludeFallback::default();
        let env = MacroClauseEnv {
            symbol_tables: &live,
            module_aliases: &aliases,
            prelude_fallback: &prelude,
            typecheck_products: &products,
            shared_state: None,
        };

        let failed_world = dashmap::DashMap::new();
        let mut failed_table = crate::code::SessionSymbolTable::new_with_params(module.clone());
        failed_table.insert(
            bad_name.clone(),
            ModuleEntry::def(
                Scheme {
                    type_vars: Vec::new(),
                    constraints: std::collections::HashMap::new(),
                    ty: Type::Fn(Vec::new(), Box::new(Type::Int)),
                },
                DefKind::UserFn {
                    fn_state: UserFnState::Concrete {
                        got_slot: 0,
                        mode_summary: None,
                    },
                },
            )
            .build(),
        );
        failed_world.insert(module.clone(), failed_table);
        let mut failed = prepared_product_turn(
            &module,
            failed_world,
            vec![(module.clone(), vec![bad_name])],
        );

        assert!(
            failed.compile_batch(0).is_err(),
            "missing settled codegen view forces the production backend path to fail"
        );
        failed.clear_reserved_slots();
        assert!(
            products.get(&module).is_none(),
            "failed macro backend compilation publishes no typecheck product"
        );

        let successful_world = dashmap::DashMap::new();
        successful_world.insert(
            module.clone(),
            crate::code::SessionSymbolTable::new_with_params(module.clone()),
        );
        let successful = prepared_product_turn(&module, successful_world, Vec::new());
        successful.publish(&env);

        let installed = products
            .get(&module)
            .expect("successful macro publication installs its settled product");
        assert!(installed.file_path.is_none());
        assert!(installed.source_text.is_none());
        assert!(installed.unresolved_dispatch.is_empty());
    }

    #[test]
    fn typed_dispatch_enrolls_specialization_not_template_or_unrelated_dollar_row() {
        use cranelisp_types::{ApplyRef, ConcreteType, MonoDefnVariant, MonoExpr, VarRef};

        let template = fq("helper", "identity");
        let dependency = fq("helper", "identity$macros.Sexp");
        let unrelated = fq("helper", "other$primitives.Int");
        let view = MonoDefnVariant {
            name: Symbol::from("__macro_wrap_clause_0"),
            params: Vec::new(),
            body: MonoExpr::Apply {
                callee: Box::new(MonoExpr::Var {
                    name: Symbol::from("identity"),
                    span: Span::SYNTHETIC,
                    resolved_call: None,
                    resolution: VarRef::Global(template.clone()),
                    ty: ConcreteType::Int,
                }),
                args: Vec::new(),
                span: Span::SYNTHETIC,
                resolved_call: None,
                dispatch: ApplyRef::Dispatch(dependency.clone()),
                ty: ConcreteType::Int,
                escapes: None,
                confined: None,
                unique_static: None,
                provenance: None,
            },
            span: Span::SYNTHETIC,
            mode_summary: None,
        };
        let mut worklist = FqWorklist::default();
        collect_codegen_dependencies(&view, &mut worklist);

        assert_eq!(worklist.pending, vec![dependency]);
        assert!(!worklist.queued.contains(&template));
        assert!(!worklist.queued.contains(&unrelated));
    }

    #[test]
    fn canonical_primitive_extern_is_by_name_leaf_but_missing_key_is_error() {
        let module = ModuleFullPath::from("macros");
        let symbol = Symbol::from("sconcat");
        let canonical = cranelisp_types::FQSymbol {
            module: module.clone(),
            symbol: symbol.clone(),
        };
        let baseline = dashmap::DashMap::new();
        let mut table = crate::code::SessionSymbolTable::new_with_params(module);
        table.insert(
            symbol,
            ModuleEntry::def(
                cranelisp_types::Scheme {
                    type_vars: Vec::new(),
                    constraints: std::collections::HashMap::new(),
                    ty: cranelisp_types::Type::Int,
                },
                cranelisp_types::DefKind::PrimitiveExtern,
            )
            .build(),
        );
        baseline.insert(ModuleFullPath::from("macros"), table);

        let (ordered, leases) = derive_macro_turn_closure(
            &baseline,
            &mut TurnDelta::default(),
            canonical,
            Span::SYNTHETIC,
        )
        .expect("canonical PrimitiveExtern is an executable by-name leaf");
        assert!(
            ordered.is_empty(),
            "by-name leaves are not codegen-enrolled"
        );
        assert!(
            leases.is_empty(),
            "static externs require no JIT owner lease"
        );

        let missing = derive_macro_turn_closure(
            &baseline,
            &mut TurnDelta::default(),
            fq("primitives", "sconcat"),
            Span::SYNTHETIC,
        )
        .expect_err("a missing FQ must not be treated as a by-name leaf");
        assert!(missing.to_string().contains("is missing"));
    }
}
