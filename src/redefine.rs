//! The redefinition guard and commit-gate classification
//! (`design/int/session-transaction.md`, authoritative; `repl/spec/18-redefinition.md`
//! is the normative UX).
//!
//! A redefinition is a guarded publication inside the ordinary prepared
//! transaction (design §0): [`validate_guarded_redefinition`] rejects a
//! declaration-class change, a visibility change, a callable language-type
//! change with a blocking dependent (§3) and an ownership-ABI change before
//! anything publishes; [`classify_redefinition`] gives the commit gate its slot
//! policy (§2, §7); and every displaced compiled owner enters the
//! [`RetentionPool`] (§6). No redefinition re-typechecks or recompiles a
//! dependent or leaves a symbol broken (§5.2). [`ReverseIndex`] serves `/refs`.

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use cranelisp_types::{
    Binding, CallableArmId, CallableOrigin, CallableTarget, CranelispError, Decl, ErrorLocation,
    FQSymbol, Life, ModuleFullPath, Realization, Scheme, Span, Symbol, Type, TypeId,
};

use crate::code::{Code, SessionSymbolTable};

mod type_structure;
pub(crate) use type_structure::{StructuralTypeChange, structural_type_change};

type SymbolTables = dashmap::DashMap<ModuleFullPath, SessionSymbolTable>;

// ---------------------------------------------------------------------------
// LanguageType — the guarded-publication semantic comparand
// ---------------------------------------------------------------------------

/// A scheme's semantic identity, independent of inference-assigned `TypeId`s.
/// This is deliberately structural: the user-facing renderer omits constraints
/// in positions where they are not printed and is therefore not an equality
/// key. Documentation, names, modes, slots and bodies are excluded.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct LanguageType {
    ty: CanonicalType,
    quantified: Vec<bool>,
    constraints: Vec<Vec<String>>,
    unused_quantified_constraints: Vec<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CanonicalType {
    Int,
    Bool,
    String,
    Float,
    Fn(Vec<CanonicalType>, Box<CanonicalType>),
    Adt(String, Vec<CanonicalType>),
    Var(usize),
    TyConApp(usize, Vec<CanonicalType>),
}

impl LanguageType {
    fn of(binding: &Binding<Code>) -> Option<Self> {
        let scheme = match &binding.declaration {
            Decl::Callable(callable) => &callable.arm.scheme,
            _ => return None,
        };
        Some(Self::of_scheme(scheme))
    }

    fn of_scheme(scheme: &Scheme) -> Self {
        let mut ids = Vec::new();
        let ty = canonical_type(&scheme.ty, &mut ids);
        let quantified_ids: HashSet<TypeId> = scheme.type_vars.iter().copied().collect();
        let quantified = ids.iter().map(|id| quantified_ids.contains(id)).collect();
        let constraints = ids
            .iter()
            .map(|id| canonical_constraints(scheme.constraints.get(id)))
            .collect();
        let mut unused_quantified_constraints = quantified_ids
            .iter()
            .filter(|id| !ids.contains(id))
            .map(|id| canonical_constraints(scheme.constraints.get(id)))
            .collect::<Vec<_>>();
        unused_quantified_constraints.sort();
        Self {
            ty,
            quantified,
            constraints,
            unused_quantified_constraints,
        }
    }
}

fn canonical_constraints(constraints: Option<&Vec<cranelisp_types::FQTraitName>>) -> Vec<String> {
    let mut names = constraints
        .into_iter()
        .flatten()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    names.sort();
    names.dedup();
    names
}

fn canonical_var(id: TypeId, ids: &mut Vec<TypeId>) -> usize {
    if let Some(index) = ids.iter().position(|candidate| *candidate == id) {
        index
    } else {
        let index = ids.len();
        ids.push(id);
        index
    }
}

fn canonical_type(ty: &Type, ids: &mut Vec<TypeId>) -> CanonicalType {
    match ty {
        Type::Int => CanonicalType::Int,
        Type::Bool => CanonicalType::Bool,
        Type::String => CanonicalType::String,
        Type::Float => CanonicalType::Float,
        Type::Fn(params, result) => CanonicalType::Fn(
            params
                .iter()
                .map(|param| canonical_type(param, ids))
                .collect(),
            Box::new(canonical_type(result, ids)),
        ),
        Type::ADT(name, args) => CanonicalType::Adt(
            name.to_string(),
            args.iter().map(|arg| canonical_type(arg, ids)).collect(),
        ),
        Type::Var(id) => CanonicalType::Var(canonical_var(*id, ids)),
        Type::TyConApp(id, args) => CanonicalType::TyConApp(
            canonical_var(*id, ids),
            args.iter().map(|arg| canonical_type(arg, ids)).collect(),
        ),
    }
}

// ---------------------------------------------------------------------------
// RedefKind + classification (design §2.1/§2.2)
// ---------------------------------------------------------------------------

/// The commit gate's three-way classification of a staged callable `Def`
/// against the prior live entry under the same name (design §2.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RedefKind {
    /// No prior live `Def` under this name — today's fresh-allocate path.
    New,
    /// Prior exists; ABI surface unchanged — today's reuse-and-patch path
    /// (late binding preserved; the L-D1 fast path).
    AbiPreserving,
    /// Prior exists; ABI surface changed — fresh slot, old slot frozen with
    /// its code retained (design §7.1).
    AbiChanging,
}

/// True iff the entry is a concrete single-sig `UserFn` `Def` — the target
/// kind per-symbol precision covers at stage M (design §2.2).
pub(crate) fn is_concrete_userfn(binding: &Binding<Code>) -> bool {
    binding.callable().is_some_and(|callable| {
        matches!(callable.origin, CallableOrigin::Plain)
            && matches!(
                callable.arm.life,
                Life::Concrete {
                    realization: Realization::Body { .. },
                    ..
                }
            )
    })
}

/// True for internal compiler artifacts the gate must never classify as
/// ABI-changing: the synthetic `__expr` wrapper (a fresh scheme every
/// expression turn — fresh-slot churn would exhaust the GOT) and macro clause
/// defns (`__macro_{name}_clause_{idx}` — internal dispatch, never a user
/// redefinition target).
pub(crate) fn is_gate_exempt_internal(name: &str) -> bool {
    name == crate::worker::SYNTHETIC_EXPR_WRAPPER || name.starts_with("__macro_")
}

/// Classify a prior live entry against its staged replacement. Ordinary
/// single- and multi-signature callables compare as one declaration class by
/// their complete language-type set (`repl/spec/18-redefinition.md` §§18.1,
/// 18.3). Another callable versions its slot only when both sides are
/// concrete single-body user functions; otherwise it patches in place.
pub(crate) fn classify_redefinition(
    name: &str,
    prior: Option<&Binding<Code>>,
    staged: &Binding<Code>,
) -> RedefKind {
    let Some(prior) = prior else {
        return RedefKind::New;
    };
    if is_gate_exempt_internal(name) {
        return RedefKind::AbiPreserving;
    }
    // A prior slot-less Def (template promoted/replaced) has no frozen slot
    // to version — fresh allocation.
    if prior.callable_got_slot().is_none() {
        return RedefKind::New;
    }
    if matches!(
        (&prior.declaration, &staged.declaration),
        (Decl::Macro(_), Decl::Macro(_))
    ) {
        return RedefKind::AbiPreserving;
    }
    // A single-signature and multi-signature `defn` are one callable class.
    // Compare their complete signature sets even when the representation
    // changes between `Callable` and `Overloaded`.
    if let (Some(prior_type), Some(staged_type)) = (
        callable_language_type(prior),
        callable_language_type(staged),
    ) {
        return if prior_type == staged_type {
            RedefKind::AbiPreserving
        } else {
            RedefKind::AbiChanging
        };
    }
    if LanguageType::of(prior).is_none() || LanguageType::of(staged).is_none() {
        return RedefKind::New;
    }
    if !(is_concrete_userfn(prior) && is_concrete_userfn(staged)) {
        return RedefKind::AbiPreserving;
    }
    if LanguageType::of(prior) == LanguageType::of(staged) {
        RedefKind::AbiPreserving
    } else {
        RedefKind::AbiChanging
    }
}

/// Enforce the S121 ordinary-callable admission rule while the live tables are
/// still untouched. Other declaration classes retain their existing path until
/// their crate-shaped waves reach this same gate.
pub(crate) fn validate_guarded_redefinition(
    symbol_tables: &SymbolTables,
    module: &ModuleFullPath,
    name: &Symbol,
    _live_table: &SessionSymbolTable,
    _staging_table: &SessionSymbolTable,
    prior: Option<&Binding<Code>>,
    staged: &Binding<Code>,
) -> Result<(), CranelispError> {
    let Some(prior) = prior else {
        return Ok(());
    };
    if is_gate_exempt_internal(name.as_ref()) {
        return Ok(());
    }

    let target = FQSymbol {
        module: module.clone(),
        symbol: name.clone(),
    };
    let prior_class = declaration_class(prior);
    let staged_class = declaration_class(staged);
    if prior_class.is_some() && staged_class.is_some() && prior_class != staged_class {
        return Err(CranelispError::TypeError {
            message: format!(
                "cannot redefine {target}: live redefinition must preserve the declaration class; use a new name or reload persisted source"
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }
    if prior_class.is_some() && prior_class == staged_class && prior.visibility != staged.visibility
    {
        return Err(CranelispError::TypeError {
            message: format!(
                "cannot redefine {target}: declaration visibility cannot change during live redefinition; use a new name or reload persisted source"
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }
    if prior_class == Some(DeclarationClass::Callable)
        && staged_class == Some(DeclarationClass::Callable)
    {
        let prior_type = callable_language_type(prior);
        let staged_type = callable_language_type(staged);
        if prior_type.is_some() && staged_type.is_some() && prior_type != staged_type {
            let blockers = blocking_dependents(symbol_tables, &target);
            if blockers.is_empty() {
                return Ok(());
            }
            return Err(type_change_rejection(
                &target,
                format_callable_language_type(prior),
                format_callable_language_type(staged),
                &blockers,
            ));
        }
    }
    if !is_concrete_userfn(prior) || !is_concrete_userfn(staged) {
        return Ok(());
    }

    let same_language_type = LanguageType::of(prior) == LanguageType::of(staged);
    if same_language_type {
        if cranelisp_types::ModeSummary::abi_eq_opt(prior.mode_summary(), staged.mode_summary()) {
            return Ok(());
        }
        return Err(CranelispError::TypeError {
            message: format!(
                "cannot redefine {target}: language type is unchanged; old ownership ABI: {}; proposed ownership ABI: {}; the proposed replacement changes the ownership ABI",
                format_ownership_abi(prior),
                format_ownership_abi(staged),
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    let blockers = blocking_dependents(symbol_tables, &target);
    if blockers.is_empty() {
        return Ok(());
    }
    Err(type_change_rejection(
        &target,
        format_callable_language_type(prior),
        format_callable_language_type(staged),
        &blockers,
    ))
}

/// Publication policy for historical instances of an admitted authored
/// callable replacement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InstanceRematerializationPolicy {
    SameLanguageType,
    CallerFreeLanguageTypeChange,
}

/// Classify an authored replacement whose historical concrete instances must
/// be rematerialized in the same prepared turn. The ordinary guard runs first;
/// this projection preserves its same-type and caller-free type-change cases.
pub(crate) fn instance_rematerialization_policy(
    symbol_tables: &SymbolTables,
    module: &ModuleFullPath,
    name: &Symbol,
    prior: &Binding<Code>,
    staged: &Binding<Code>,
) -> Option<InstanceRematerializationPolicy> {
    if declaration_class(prior) != Some(DeclarationClass::Callable)
        || declaration_class(staged) != Some(DeclarationClass::Callable)
    {
        return None;
    }
    let Some(prior_type) = callable_language_type(prior) else {
        return None;
    };
    let Some(staged_type) = callable_language_type(staged) else {
        return None;
    };
    if prior_type == staged_type {
        return Some(InstanceRematerializationPolicy::SameLanguageType);
    }
    let target = FQSymbol {
        module: module.clone(),
        symbol: name.clone(),
    };
    blocking_dependents(symbol_tables, &target)
        .is_empty()
        .then_some(InstanceRematerializationPolicy::CallerFreeLanguageTypeChange)
}

/// Match one historical overload arm to the unique staged arm with the same
/// canonical authored language type. Arm ids are generation-local roster
/// positions and therefore cannot be carried across a replacement.
pub(crate) fn match_replacement_overload_arm(
    owner: &FQSymbol,
    prior: &Binding<Code>,
    staged: &Binding<Code>,
    prior_arm: CallableArmId,
) -> Result<CallableArmId, CranelispError> {
    let (Decl::Overloaded(prior), Decl::Overloaded(staged)) =
        (&prior.declaration, &staged.declaration)
    else {
        return Err(CranelispError::TypeError {
            message: format!(
                "cannot rematerialize prior overload instance for {owner}: replacement is not the same callable family class"
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    };
    let old = prior
        .arms
        .get(prior_arm.ordinal())
        .filter(|arm| arm.id == prior_arm)
        .ok_or_else(|| CranelispError::TypeError {
            message: format!(
                "cannot rematerialize prior overload instance for {owner}: historical arm {} is absent",
                prior_arm.ordinal()
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
    let old_type = LanguageType::of_scheme(&old.callable.scheme);
    let matches = staged
        .arms
        .iter()
        .filter(|arm| LanguageType::of_scheme(&arm.callable.scheme) == old_type)
        .map(|arm| arm.id)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [matched] => Ok(*matched),
        [] => Err(CranelispError::TypeError {
            message: format!(
                "cannot rematerialize prior overload instance for {owner}: historical arm {} has no matching staged language type",
                prior_arm.ordinal()
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
        _ => Err(CranelispError::TypeError {
            message: format!(
                "cannot rematerialize prior overload instance for {owner}: historical arm {} matches more than one staged language type",
                prior_arm.ordinal()
            ),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
    }
}

fn type_change_rejection(
    target: &FQSymbol,
    old_type: String,
    proposed_type: String,
    blockers: &[FQSymbol],
) -> CranelispError {
    let blockers = blockers
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    CranelispError::TypeError {
        message: format!(
            "cannot redefine {target}; old language type: {old_type}; proposed language type: {proposed_type}; blocking dependents: {blockers}; retain the old type or introduce a new name"
        ),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeclarationClass {
    Callable,
    Macro,
    Type,
    Trait,
    Impl,
}

fn declaration_class(binding: &Binding<Code>) -> Option<DeclarationClass> {
    match &binding.declaration {
        Decl::Callable(callable) if matches!(callable.origin, CallableOrigin::Plain) => {
            Some(DeclarationClass::Callable)
        }
        Decl::Overloaded(_) => Some(DeclarationClass::Callable),
        Decl::Macro(_) => Some(DeclarationClass::Macro),
        Decl::Type(_) => Some(DeclarationClass::Type),
        Decl::Trait(_) => Some(DeclarationClass::Trait),
        Decl::ImplShell(_) => Some(DeclarationClass::Impl),
        Decl::Callable(_) | Decl::TraitMethod(_) | Decl::SpecialForm(_) => None,
    }
}

fn callable_language_type(binding: &Binding<Code>) -> Option<Vec<LanguageType>> {
    match &binding.declaration {
        Decl::Callable(callable) if matches!(callable.origin, CallableOrigin::Plain) => {
            Some(vec![LanguageType::of_scheme(&callable.arm.scheme)])
        }
        Decl::Overloaded(declaration) => {
            let mut signatures = declaration
                .arms
                .iter()
                .map(|arm| LanguageType::of_scheme(&arm.callable.scheme))
                .collect::<Vec<_>>();
            signatures.sort();
            signatures.dedup();
            Some(signatures)
        }
        _ => None,
    }
}

fn format_callable_language_type(binding: &Binding<Code>) -> String {
    match &binding.declaration {
        Decl::Callable(callable) => crate::display::format_scheme_type(&callable.arm.scheme),
        Decl::Overloaded(declaration) => {
            let mut signatures = declaration
                .arms
                .iter()
                .map(|arm| crate::display::format_scheme_type(&arm.callable.scheme))
                .collect::<Vec<_>>();
            signatures.sort();
            format!("{{{}}}", signatures.join(", "))
        }
        _ => "<non-callable>".to_string(),
    }
}

fn format_ownership_abi(binding: &Binding<Code>) -> String {
    let arity = binding
        .callable()
        .and_then(|callable| match &callable.arm.scheme.ty {
            Type::Fn(params, _) => Some(params.len()),
            _ => None,
        })
        .unwrap_or_default();
    match binding.mode_summary() {
        Some(summary) => {
            let params = (0..arity)
                .map(|index| format!("{:?}", summary.param_mode(index)))
                .collect::<Vec<_>>()
                .join(", ");
            format!("params [{params}], result {:?}", summary.result)
        }
        None => {
            let params = std::iter::repeat_n("Owned", arity)
                .collect::<Vec<_>>()
                .join(", ");
            format!("params [{params}], result Fresh")
        }
    }
}

/// Reverse-scan the one durable dependency fact (`Binding::callees`) and fold
/// storage identities to their authored callable owner before comparing or
/// reporting them. There is intentionally no parallel callers index.
fn blocking_dependents(symbol_tables: &SymbolTables, target: &FQSymbol) -> Vec<FQSymbol> {
    let mut immediate_owners = HashMap::new();
    let mut edges = Vec::new();
    for table in symbol_tables.iter() {
        let module = table.key().clone();
        for (name, binding) in table.value().all_symbols() {
            let caller = FQSymbol {
                module: module.clone(),
                symbol: name.clone(),
            };
            immediate_owners.insert(caller.clone(), immediate_callable_owner(&caller, binding));
            let callees: Vec<FQSymbol> = crate::callee_edges::binding_callees(binding)
                .cloned()
                .collect();
            if !callees.is_empty() {
                edges.push((caller, callees));
            }
        }
    }

    let target = normalize_callable_owner(target, &immediate_owners);
    let mut blockers = HashSet::new();
    for (caller, callees) in edges {
        if caller.symbol.as_ref() == crate::worker::SYNTHETIC_EXPR_WRAPPER {
            continue;
        }
        let caller = normalize_callable_owner(&caller, &immediate_owners);
        if caller == target {
            continue;
        }
        if callees
            .iter()
            .map(|callee| normalize_callable_owner(callee, &immediate_owners))
            .any(|callee| callee == target)
        {
            blockers.insert(caller);
        }
    }
    let mut blockers = blockers.into_iter().collect::<Vec<_>>();
    blockers.sort_by_key(ToString::to_string);
    blockers
}

fn immediate_callable_owner(fq: &FQSymbol, binding: &Binding<Code>) -> FQSymbol {
    let Some(callable) = binding.callable() else {
        return fq.clone();
    };
    if let Life::Concrete {
        minted_from: Some(link),
        ..
    } = &callable.arm.life
    {
        return match &link.template {
            CallableTarget::Binding(owner)
            | CallableTarget::OverloadArm { owner, .. }
            | CallableTarget::MacroClause { owner, .. } => owner.clone(),
            _ => fq.clone(),
        };
    }
    fq.clone()
}

fn normalize_callable_owner(
    fq: &FQSymbol,
    immediate_owners: &HashMap<FQSymbol, FQSymbol>,
) -> FQSymbol {
    let mut current = fq.clone();
    let mut seen = HashSet::new();
    while seen.insert(current.clone()) {
        let Some(next) = immediate_owners.get(&current) else {
            break;
        };
        if next == &current {
            break;
        }
        current = next.clone();
    }
    current
}

// ---------------------------------------------------------------------------
// Retention pool (design §6.1)
// ---------------------------------------------------------------------------

/// One displaced code handle, kept until session end so in-flight frames,
/// heap closures and old-ABI chains that still embed its slot stay mapped
/// (design §6.2). Reclaimed wholesale at session end (the `kept_dlls`
/// precedent).
pub(crate) struct RetainedCode {
    /// Whose supersession this is (observability).
    #[allow(dead_code)]
    pub fq: FQSymbol,
    #[allow(dead_code)]
    pub module: ModuleFullPath,
    /// The frozen slot (`None` for code displaced off a slot-less entry).
    #[allow(dead_code)]
    pub slot: Option<usize>,
    /// The retention handle (`Arc<Jit>`/`Arc<Linker>` keeps pages mapped).
    #[allow(dead_code)]
    pub code: Code,
}

impl RetainedCode {
    /// A pool entry for a `Code` displaced from `module`/`name`.
    pub(crate) fn frozen(
        module: &ModuleFullPath,
        name: &Symbol,
        slot: Option<usize>,
        code: Code,
    ) -> Self {
        Self {
            fq: FQSymbol {
                module: module.clone(),
                symbol: name.clone(),
            },
            module: module.clone(),
            slot,
            code,
        }
    }
}

/// The session retention pool (`SharedState.retained_code`).
pub(crate) type RetentionPool = Mutex<Vec<RetainedCode>>;

// ---------------------------------------------------------------------------
// Reverse dependency index (design §3.3)
// ---------------------------------------------------------------------------

fn instance_template_owner(binding: &Binding<Code>) -> Option<FQSymbol> {
    let callable = binding.callable()?;
    let Life::Concrete {
        minted_from: Some(link),
        ..
    } = &callable.arm.life
    else {
        return None;
    };
    match &link.template {
        CallableTarget::Binding(owner) | CallableTarget::OverloadArm { owner, .. } => {
            Some(owner.clone())
        }
        CallableTarget::MacroClause { .. } => None,
        _ => None,
    }
}

/// Callee → callers, derived on demand from `Def.callees` across the live
/// tables at the moment an `AbiChanging` classification fires. Never a
/// second authored store (Principle 7): a scan is correct by construction
/// against whatever the tables hold now, and costs nothing on the body-only
/// fast path (L-D1 — no incremental maintenance tax on registrations).
pub(crate) struct ReverseIndex {
    map: HashMap<FQSymbol, Vec<FQSymbol>>,
    instance_owners: HashMap<FQSymbol, FQSymbol>,
}

impl ReverseIndex {
    pub(crate) fn build(tables: &SymbolTables) -> Self {
        let mut map: HashMap<FQSymbol, Vec<FQSymbol>> = HashMap::new();
        let mut instance_owners = HashMap::new();
        for shard in tables.iter() {
            let module = shard.key().clone();
            for (name, entry) in shard.value().all_symbols() {
                if let Some(owner) = instance_template_owner(entry) {
                    instance_owners.insert(
                        FQSymbol {
                            module: module.clone(),
                            symbol: name.clone(),
                        },
                        owner,
                    );
                }
            }
        }
        for shard in tables.iter() {
            let module = shard.key().clone();
            for (name, entry) in shard.value().all_symbols() {
                // The synthetic `__expr` eval wrapper is never a caller
                // (FIXME 0491): each expression turn redefines it, so a stale
                // wrapper is never re-invoked. A compiled macro clause persists
                // and is re-invoked at the next expansion, so it stays.
                if name.as_ref() == crate::worker::SYNTHETIC_EXPR_WRAPPER {
                    continue;
                }
                let callees = entry.callees();
                if callees.is_empty() {
                    continue;
                }
                let caller = FQSymbol {
                    module: module.clone(),
                    symbol: name.clone(),
                };
                for callee in callees {
                    map.entry(callee.clone()).or_default().push(caller.clone());
                }
            }
        }
        // Deterministic caller order (HashMap iteration is seed-randomised).
        for callers in map.values_mut() {
            callers.sort_by(|a, b| {
                (a.module.as_ref(), a.symbol.as_ref()).cmp(&(b.module.as_ref(), b.symbol.as_ref()))
            });
            callers.dedup();
        }
        ReverseIndex {
            map,
            instance_owners,
        }
    }

    /// Callers of `target` and of its `$`-mangled variants (a mangled callee
    /// whose base is `target` — mono instances minted from the template),
    /// unioned, sorted, deduped: a caller of a minted instance refers to the
    /// template as surely as a direct caller does.
    pub(crate) fn callers_of_with_variants(&self, target: &FQSymbol) -> Vec<FQSymbol> {
        let mut out: Vec<FQSymbol> = Vec::new();
        for (callee, callers) in &self.map {
            if callee == target || self.base_fq(callee) == *target {
                out.extend(callers.iter().cloned());
            }
        }
        out.sort_by(|a, b| {
            (a.module.as_ref(), a.symbol.as_ref()).cmp(&(b.module.as_ref(), b.symbol.as_ref()))
        });
        out.dedup();
        out
    }

    fn base_fq(&self, fq: &FQSymbol) -> FQSymbol {
        self.instance_owners
            .get(fq)
            .cloned()
            .unwrap_or_else(|| base_fq(fq))
    }
}

/// Strip a `$`-mangled variant name to its base defn FQ.
pub(crate) fn base_fq(fq: &FQSymbol) -> FQSymbol {
    match fq.symbol.as_ref().split_once('$') {
        Some((base, _)) => FQSymbol {
            module: fq.module.clone(),
            symbol: Symbol::from(base),
        },
        None => fq.clone(),
    }
}

/// Resolve a concrete instance row to its authored template owner using the
/// stored backlink. Legacy `$`-generated rows retain the spelling fallback for
/// the non-instance implementation and macro artifacts that still use it.
pub(crate) fn base_fq_from_tables(tables: &SymbolTables, fq: &FQSymbol) -> FQSymbol {
    tables
        .get(&fq.module)
        .and_then(|table| {
            table
                .get(fq.symbol.as_ref())
                .and_then(instance_template_owner)
        })
        .unwrap_or_else(|| base_fq(fq))
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{
        CallableArm, CallableOrigin, CallableTarget, ConcreteType, DefnVariant, Expr, FQTraitName,
        InstanceLink, Life, MonoDefnVariant, OverloadedCallable, Scheme, TemplateBody,
        TemplateKind, TraitName, Type, Visibility,
    };
    use std::collections::HashMap as StdHashMap;

    fn scheme(ty: Type) -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: StdHashMap::new(),
            ty,
        }
    }

    fn variant() -> DefnVariant {
        DefnVariant {
            params: Vec::new(),
            body: Expr::IntLit {
                value: 0,
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(Type::Int)),
            },
            span: Span::SYNTHETIC,
        }
    }

    fn install_concrete_fixture(
        table: &mut SessionSymbolTable,
        name: &str,
        ty: Type,
        callees: Vec<FQSymbol>,
        expected_slot: usize,
    ) {
        while table
            .all_symbols()
            .filter_map(|(_, b)| b.callable_got_slot())
            .count()
            < expected_slot
        {
            let index = table
                .all_symbols()
                .filter_map(|(_, b)| b.callable_got_slot())
                .count();
            install_concrete_fixture(
                table,
                &format!("__padding_{index}"),
                Type::Int,
                Vec::new(),
                index,
            );
        }
        let ast = variant();
        let view = MonoDefnVariant {
            name: Symbol::from(name),
            params: Vec::new(),
            body: cranelisp_types::MonoExpr::lenient_from_expr(
                &ast.body,
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
                scheme(ty),
                Vec::new(),
                None,
                0,
                CallableOrigin::Plain,
                Realization::Body { view, code: None },
                Some(ast),
                callees,
                Visibility::Public,
            )
            .expect("concrete fixture installs through lifecycle funnel");
        assert_eq!(slot.index(), expected_slot);
    }

    fn install_template_fixture(
        table: &mut SessionSymbolTable,
        name: &str,
        callees: Vec<FQSymbol>,
    ) {
        table
            .install_template(
                Symbol::from(name),
                template_fixture_scheme(),
                Vec::new(),
                None,
                0,
                CallableOrigin::Plain,
                TemplateBody::Ast(variant()),
                TemplateKind::Parametric,
                callees,
                Visibility::Public,
            )
            .expect("template fixture installs through lifecycle funnel");
    }

    fn template_fixture_scheme() -> Scheme {
        Scheme {
            type_vars: vec![0],
            constraints: StdHashMap::new(),
            ty: fn_ty(Vec::new(), fn_ty(vec![Type::Var(0)], Type::Int)),
        }
    }

    fn instance_fixture_link(template: FQSymbol, arg: ConcreteType) -> InstanceLink {
        InstanceLink::from_type_args(CallableTarget::Binding(template), vec![arg])
    }

    fn instance_fixture_key(link: &InstanceLink) -> Symbol {
        link.instance_key(&template_fixture_scheme())
            .expect("fixture template and substitution form a callable key")
    }

    fn install_instance_fixture(
        table: &mut SessionSymbolTable,
        template: FQSymbol,
        arg: ConcreteType,
        callees: Vec<FQSymbol>,
    ) {
        let link = instance_fixture_link(template, arg.clone());
        let name = instance_fixture_key(&link);
        let result_ty = fn_ty(vec![arg.to_type()], Type::Int);
        let ast = DefnVariant {
            params: Vec::new(),
            body: Expr::Lambda {
                params: vec![(Symbol::from("y"), None)],
                body: Box::new(variant().body),
                span: Span::SYNTHETIC,
                inferred_type: Some(Box::new(result_ty.clone())),
            },
            span: Span::SYNTHETIC,
        };
        let view = MonoDefnVariant {
            name,
            params: Vec::new(),
            body: cranelisp_types::MonoExpr::lenient_from_expr(
                &ast.body,
                &Default::default(),
                &Default::default(),
                &Default::default(),
            ),
            span: Span::SYNTHETIC,
            mode_summary: None,
        };
        table
            .install_instance(
                link,
                scheme(fn_ty(Vec::new(), result_ty)),
                Vec::new(),
                None,
                0,
                CallableOrigin::Plain,
                Realization::Body { view, code: None },
                Some(ast),
                callees,
                Visibility::Public,
            )
            .expect("instance fixture installs through lifecycle funnel");
    }

    fn concrete_def(ty: Type, slot: usize) -> Binding<Code> {
        let mut table = SessionSymbolTable::new_with_params(ModuleFullPath::from("fixture"));
        let mut type_vars: Vec<_> = cranelisp_types::free_vars(&ty).into_iter().collect();
        type_vars.sort_unstable();
        if type_vars.is_empty() {
            install_concrete_fixture(&mut table, "target", ty, Vec::new(), slot);
        } else {
            table
                .install_template(
                    Symbol::from("target"),
                    Scheme {
                        type_vars,
                        constraints: StdHashMap::new(),
                        ty,
                    },
                    Vec::new(),
                    None,
                    0,
                    CallableOrigin::Plain,
                    TemplateBody::Ast(variant()),
                    TemplateKind::Parametric,
                    Vec::new(),
                    Visibility::Public,
                )
                .expect("polymorphic fixture installs through lifecycle funnel");
        }
        table.get("target").expect("fixture installed").clone()
    }

    fn overloaded(types: Vec<Type>) -> Binding<Code> {
        let arms = types
            .into_iter()
            .map(|ty| CallableArm::new(scheme(ty), Vec::new(), Life::Declared { prior: None }))
            .collect();
        Binding::new(
            Decl::Overloaded(
                OverloadedCallable::new(None, 0, arms)
                    .expect("overload fixture has a valid roster"),
            ),
            Visibility::Public,
        )
    }

    fn fq(module: &str, name: &str) -> FQSymbol {
        FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(name),
        }
    }

    fn fn_ty(params: Vec<Type>, ret: Type) -> Type {
        Type::Fn(params, Box::new(ret))
    }

    // spec: repl/spec/18-redefinition.md §18.1 — language types compare
    // modulo alpha-renaming of bound type variables.
    #[test]
    fn language_type_alpha_canonical_var_ids_compare_equal() {
        let a = concrete_def(fn_ty(vec![Type::Var(3)], Type::Var(3)), 0);
        let b = concrete_def(fn_ty(vec![Type::Var(97)], Type::Var(97)), 1);
        assert_eq!(
            LanguageType::of(&a),
            LanguageType::of(&b),
            "alpha-equivalent schemes must have the same language type"
        );
    }

    // spec: repl/spec/18-redefinition.md §18.1 — slot identity is not part of
    // the language type, while a structural type change is.
    #[test]
    fn language_type_ignores_slot_but_detects_structure() {
        let int_fn = concrete_def(fn_ty(vec![Type::Int], Type::Int), 0);
        let int_fn_other_slot = concrete_def(fn_ty(vec![Type::Int], Type::Int), 7);
        let str_fn = concrete_def(fn_ty(vec![Type::String], Type::Int), 0);
        assert_eq!(
            LanguageType::of(&int_fn),
            LanguageType::of(&int_fn_other_slot)
        );
        assert_ne!(LanguageType::of(&int_fn), LanguageType::of(&str_fn));
    }

    // spec: repl/spec/18-redefinition.md §18.1 — the fully resolved scheme,
    // including its constraint set, is the language type. Trait order and
    // inference-assigned ids do not change it.
    #[test]
    fn language_type_canonicalizes_constraints_without_dropping_them() {
        let trait_name =
            |name| FQTraitName::new(ModuleFullPath::from("traits"), TraitName::from(name));
        let make = |id, traits: Vec<FQTraitName>| Scheme {
            type_vars: vec![id],
            constraints: StdHashMap::from([(id, traits)]),
            ty: fn_ty(vec![Type::Var(id)], Type::Var(id)),
        };
        let a = make(3, vec![trait_name("Ord"), trait_name("Eq")]);
        let b = make(97, vec![trait_name("Eq"), trait_name("Ord")]);
        let different = make(41, vec![trait_name("Eq")]);

        assert_eq!(LanguageType::of_scheme(&a), LanguageType::of_scheme(&b));
        assert_ne!(
            LanguageType::of_scheme(&a),
            LanguageType::of_scheme(&different)
        );
    }

    // spec: repl/spec/18-redefinition.md §18.1; design/int/session-transaction.md
    // §5.2 (Unit evidence) — a language-type change of `f` is blocked by every
    // binding whose recorded callees name it: a concrete body and a template
    // that has no realisation. With no caller nothing blocks it.
    #[test]
    fn concrete_and_unrealised_template_callers_block_a_type_change() {
        let target = fq("user", "f");
        let tables = SymbolTables::new();
        let mut user = SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        install_concrete_fixture(&mut user, "f", fn_ty(vec![Type::Int], Type::Int), vec![], 0);
        install_concrete_fixture(
            &mut user,
            "concrete-caller",
            fn_ty(vec![Type::Int], Type::Int),
            vec![target.clone()],
            1,
        );
        install_template_fixture(&mut user, "template-caller", vec![target.clone()]);
        tables.insert(ModuleFullPath::from("user"), user);
        assert_eq!(
            blocking_dependents(&tables, &target),
            vec![fq("user", "concrete-caller"), fq("user", "template-caller")]
        );

        let alone = SymbolTables::new();
        let mut user = SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        install_concrete_fixture(&mut user, "f", fn_ty(vec![Type::Int], Type::Int), vec![], 0);
        alone.insert(ModuleFullPath::from("user"), user);
        assert!(
            blocking_dependents(&alone, &target).is_empty(),
            "control: with no caller the change is admitted"
        );
    }

    // spec: repl/spec/18-redefinition.md §18.2 — caller discovery is a
    // reverse scan of settled callee edges. It excludes only the target's own
    // self-edge, not codegen-pending definitions, and folds realizations to one
    // authored owner before sorting and deduplication.
    #[test]
    fn blockers_are_direct_settled_normalized_and_sorted() {
        let tables = SymbolTables::new();
        let mut user = SessionSymbolTable::new_with_params(ModuleFullPath::from("user"));
        let target = fq("user", "f");
        install_concrete_fixture(
            &mut user,
            "f",
            fn_ty(vec![Type::Int], Type::Int),
            vec![target.clone()],
            0,
        );
        install_concrete_fixture(
            &mut user,
            "z-direct",
            fn_ty(vec![Type::Int], Type::Int),
            vec![target.clone()],
            1,
        );
        install_concrete_fixture(
            &mut user,
            "transitive-only",
            fn_ty(vec![Type::Int], Type::Int),
            vec![fq("user", "z-direct")],
            2,
        );
        install_template_fixture(&mut user, "poly", Vec::new());
        install_instance_fixture(
            &mut user,
            fq("user", "poly"),
            ConcreteType::Int,
            vec![target.clone()],
        );
        install_instance_fixture(
            &mut user,
            fq("user", "poly"),
            ConcreteType::String,
            vec![target.clone()],
        );
        tables.insert(ModuleFullPath::from("user"), user);

        assert_eq!(
            blocking_dependents(&tables, &target)
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            vec!["user/poly", "user/z-direct"]
        );
    }

    // spec: design/int/session-transaction.md §2.1 — RedefKind classification:
    // New (no prior), AbiPreserving (same surface), AbiChanging (changed).
    #[test]
    fn classify_new_preserving_changing() {
        let prior = concrete_def(fn_ty(vec![Type::Int], Type::Int), 0);
        let same = concrete_def(fn_ty(vec![Type::Int], Type::Int), 0);
        let changed = concrete_def(fn_ty(vec![Type::String], Type::Int), 0);

        assert_eq!(classify_redefinition("f", None, &same), RedefKind::New);
        assert_eq!(
            classify_redefinition("f", Some(&prior), &same),
            RedefKind::AbiPreserving
        );
        assert_eq!(
            classify_redefinition("f", Some(&prior), &changed),
            RedefKind::AbiChanging
        );
    }

    // spec: repl/spec/18-redefinition.md §§18.1, 18.3 — internal artifacts
    // (`__expr`, macro clauses) never classify AbiChanging, while single- and
    // multi-signature declarations compare as one callable class.
    #[test]
    fn classify_internal_names_and_callable_family_boundaries() {
        let prior = concrete_def(fn_ty(vec![Type::Int], Type::Int), 0);
        let changed = concrete_def(fn_ty(vec![Type::String], Type::String), 0);
        assert_eq!(
            classify_redefinition("__expr", Some(&prior), &changed),
            RedefKind::AbiPreserving
        );
        assert_eq!(
            classify_redefinition("__macro_m_clause_0", Some(&prior), &changed),
            RedefKind::AbiPreserving
        );
        // Prior slot-less (template) → New (no frozen slot to version).
        let slotless_prior = concrete_def(fn_ty(vec![Type::Var(0)], Type::Var(0)), 0);
        assert_eq!(
            classify_redefinition("f", Some(&slotless_prior), &changed),
            RedefKind::New
        );
        // Changing representation without changing the signature set keeps the
        // language type. Adding a signature changes the whole family type.
        let same_family = overloaded(vec![fn_ty(vec![Type::Int], Type::Int)]);
        assert_eq!(
            classify_redefinition("f", Some(&prior), &same_family),
            RedefKind::AbiPreserving
        );
        let changed_family = overloaded(vec![
            fn_ty(vec![Type::Int], Type::Int),
            fn_ty(vec![Type::Int, Type::Int], Type::Int),
        ]);
        assert_eq!(
            classify_redefinition("f", Some(&prior), &changed_family),
            RedefKind::AbiChanging
        );
    }

    // spec: design/int/session-transaction.md §3.3 — the reverse index is
    // derived from `Def.callees` (callee → callers), across modules.
    #[test]
    fn reverse_index_lists_direct_callers_across_modules() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user = ModuleFullPath::from("user");
        let other = ModuleFullPath::from("other");
        let mut ut = SessionSymbolTable::new_with_params(user.clone());
        // g calls f; h calls g; unrelated calls add-i64 only.
        install_concrete_fixture(&mut ut, "f", Type::Int, vec![], 0);
        install_concrete_fixture(&mut ut, "g", Type::Int, vec![fq("user", "f")], 1);
        install_concrete_fixture(&mut ut, "h", Type::Int, vec![fq("user", "g")], 2);
        install_concrete_fixture(
            &mut ut,
            "unrelated",
            Type::Int,
            vec![fq("primitives", "add-i64")],
            3,
        );
        tables.insert(user.clone(), ut);
        let mut ot = SessionSymbolTable::new_with_params(other.clone());
        install_concrete_fixture(&mut ot, "x", Type::Int, vec![fq("user", "f")], 0);
        tables.insert(other, ot);

        let reverse = ReverseIndex::build(&tables);
        let callers = reverse.callers_of_with_variants(&fq("user", "f"));
        assert_eq!(
            callers,
            vec![fq("other", "x"), fq("user", "g")],
            "direct callers only, across modules; `h` and `unrelated` are not"
        );
    }

    // spec: repl/spec/03-slash-commands.md (`/refs`); FIXME 0491 — the
    // synthetic `__expr` eval wrapper never joins the reverse index as a
    // caller; a macro clause with a real callee edge does.
    #[test]
    fn reverse_index_neg_excludes_only_expr_keeps_macro_clause() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user = ModuleFullPath::from("user");
        let mut ut = SessionSymbolTable::new_with_params(user.clone());
        install_concrete_fixture(&mut ut, "f", Type::Int, vec![], 0);
        // The eval wrapper — EXCLUDED (the 0491 rule, `__expr`-only).
        install_concrete_fixture(&mut ut, "__expr", Type::Int, vec![fq("user", "f")], 1);
        // A macro clause carrying a REAL callee edge to f — KEPT (F3).
        install_concrete_fixture(
            &mut ut,
            "__macro_m_clause_0",
            Type::Int,
            vec![fq("user", "f")],
            2,
        );
        // Control: a real caller with the same edge stays in.
        install_concrete_fixture(&mut ut, "g", Type::Int, vec![fq("user", "f")], 3);
        tables.insert(user.clone(), ut);

        let reverse = ReverseIndex::build(&tables);
        // `__expr` excluded; `__macro_m_clause_0` and `g` both indexed (sorted
        // by symbol — `_` < `g`).
        assert_eq!(
            reverse.callers_of_with_variants(&fq("user", "f")),
            vec![fq("user", "__macro_m_clause_0"), fq("user", "g")],
            "the eval wrapper is excluded; the macro clause is kept"
        );
    }

    // spec: design/int/session-transaction.md §"GOT exhaustion" (obligation 3)
    // — the session's allocation chokepoint surfaces exhaustion as an error,
    // never release-mode UB at slot GOT_TABLE_SIZE.
    #[test]
    fn got_exhaustion_surfaces_error_not_ub() {
        use cranelisp_types::GOT_TABLE_SIZE;
        let module = ModuleFullPath::from("user");
        let mut st = SessionSymbolTable::new_with_params(module.clone());
        for slot in 0..GOT_TABLE_SIZE {
            install_concrete_fixture(&mut st, &format!("f{slot}"), Type::Int, Vec::new(), slot);
        }
        let ast = variant();
        let view = MonoDefnVariant {
            name: Symbol::from("overflow"),
            params: Vec::new(),
            body: cranelisp_types::MonoExpr::lenient_from_expr(
                &ast.body,
                &Default::default(),
                &Default::default(),
                &Default::default(),
            ),
            span: Span::SYNTHETIC,
            mode_summary: None,
        };
        let err = st
            .install_concrete(
                Symbol::from("overflow"),
                scheme(Type::Int),
                Vec::new(),
                None,
                0,
                CallableOrigin::Plain,
                Realization::Body { view, code: None },
                Some(ast),
                Vec::new(),
                Visibility::Public,
            )
            .expect_err("slot GOT_TABLE_SIZE must be refused");
        assert!(
            err.to_string().contains("GOT slot table exhausted"),
            "got: {err}"
        );
        assert_eq!(st.all_symbols().count(), GOT_TABLE_SIZE);
    }
}
