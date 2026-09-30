use serde::{Deserialize, Serialize};

use crate::{
    CallableSlot, ConcreteType, DefnVariant, FQSymbol, FQTraitName, FQTypeName, LinkerSymbol,
    MacroParam, ModeSummary, MonoDefnVariant, SchedulingClass, Scheme, Sexp, Span, Symbol,
    TraitDeclInfo, Type, TypeDefInfo,
};

/// One name in a module's symbol table.
///
/// Visibility belongs to the binding rather than to any particular facet so
/// resolution can apply it without inspecting the declaration payload.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[non_exhaustive]
pub struct Binding<C: crate::CodeStore = ()> {
    /// Visibility of this name from modules outside its defining subtree.
    pub visibility: crate::Visibility,
    /// Terminal declaration owned by this canonical name.
    pub declaration: Decl<C>,
}

impl<C: crate::CodeStore> Binding<C> {
    /// Wrap a terminal declaration in its name-level visibility.
    pub fn new(declaration: Decl<C>, visibility: crate::Visibility) -> Self {
        Self {
            visibility,
            declaration,
        }
    }

    /// Whether this binding is visible outside its defining module subtree.
    pub fn is_public(&self) -> bool {
        self.visibility == crate::Visibility::Public
    }

    /// Project the callable facet, if this binding declares one.
    pub fn callable(&self) -> Option<&Callable<C>> {
        match &self.declaration {
            Decl::Callable(callable) => Some(callable),
            _ => None,
        }
    }

    /// Project an unslotted trait-method dispatch declaration, if present.
    pub fn trait_method(&self) -> Option<&TraitMethodRecord> {
        match &self.declaration {
            Decl::TraitMethod(record) => Some(record),
            _ => None,
        }
    }

    pub(crate) fn callable_mut(&mut self) -> Option<&mut Callable<C>> {
        match &mut self.declaration {
            Decl::Callable(callable) => Some(callable),
            _ => None,
        }
    }

    /// Project the dispatchable GOT index carried by a concrete or broken callable.
    pub fn callable_got_slot(&self) -> Option<usize> {
        match self.callable().map(|callable| &callable.arm.life) {
            Some(Life::Concrete { slot, .. } | Life::Broken { slot, .. }) => Some(slot.index()),
            _ => None,
        }
    }

    /// Whether reference resolution may stop on this callable binding.
    pub fn is_callable_target(&self) -> bool {
        self.trait_method().is_some()
            || self
                .callable()
                .is_some_and(|callable| callable.arm.life.is_callable_target())
    }

    /// Project defined-type metadata from a type declaration or product ctor facet.
    pub fn type_def_info(&self) -> Option<&TypeDefInfo> {
        match &self.declaration {
            Decl::Type(TypeRecord::Defined { info, .. }) => Some(info),
            Decl::Callable(Callable {
                origin:
                    CallableOrigin::Ctor {
                        type_def: Some(info),
                        ..
                    },
                ..
            }) => Some(info),
            _ => None,
        }
    }

    /// Project the optional ownership summary of a concrete or inline callable.
    pub fn mode_summary(&self) -> Option<&ModeSummary> {
        match self.callable()?.arm.life {
            Life::Concrete {
                ref mode_summary, ..
            }
            | Life::Inline {
                ref mode_summary, ..
            } => mode_summary.as_ref(),
            _ => None,
        }
    }

    /// Whether a concrete callable is used in first-class value position.
    pub fn value_use(&self) -> bool {
        matches!(
            self.callable().map(|callable| &callable.arm.life),
            Some(Life::Concrete {
                value_use: true,
                ..
            })
        )
    }

    /// Project the backend-emitted body view of a concrete callable.
    pub fn codegen_view(&self) -> Option<&MonoDefnVariant> {
        match self.callable()?.arm.life {
            Life::Concrete {
                realization: Realization::Body { ref view, .. },
                ..
            } => Some(view),
            _ => None,
        }
    }

    /// Project call-graph edges carried by a template or concrete callable.
    pub fn callees(&self) -> &[FQSymbol] {
        match self.callable().map(|callable| &callable.arm.life) {
            Some(Life::Template { callees, .. }) | Some(Life::Concrete { callees, .. }) => callees,
            _ => &[],
        }
    }
}

impl Binding<()> {
    pub(crate) fn into_concrete<C: crate::CodeStore>(self) -> Binding<C> {
        Binding {
            visibility: self.visibility,
            declaration: self.declaration.into_concrete(),
        }
    }
}

impl Decl<()> {
    fn into_concrete<C: crate::CodeStore>(self) -> Decl<C> {
        match self {
            Decl::Callable(callable) => Decl::Callable(callable.into_concrete()),
            Decl::TraitMethod(record) => Decl::TraitMethod(record),
            Decl::Overloaded(declaration) => Decl::Overloaded(declaration.into_concrete()),
            Decl::Macro(declaration) => Decl::Macro(declaration.into_concrete()),
            Decl::Type(record) => Decl::Type(record),
            Decl::Trait(record) => Decl::Trait(record),
            Decl::ImplShell(shell) => Decl::ImplShell(shell),
            Decl::SpecialForm(record) => Decl::SpecialForm(record),
        }
    }
}

impl Callable<()> {
    fn into_concrete<C: crate::CodeStore>(self) -> Callable<C> {
        Callable {
            docstring: self.docstring,
            seq: self.seq,
            origin: self.origin,
            arm: self.arm.into_concrete(),
        }
    }
}

impl CallableArm<()> {
    fn into_concrete<C: crate::CodeStore>(self) -> CallableArm<C> {
        CallableArm {
            scheme: self.scheme,
            param_names: self.param_names,
            life: self.life.into_concrete(),
        }
    }
}

impl OverloadedCallable<()> {
    fn into_concrete<C: crate::CodeStore>(self) -> OverloadedCallable<C> {
        OverloadedCallable {
            docstring: self.docstring,
            seq: self.seq,
            arms: self
                .arms
                .into_iter()
                .map(|arm| OverloadArm {
                    id: arm.id,
                    callable: arm.callable.into_concrete(),
                })
                .collect(),
        }
    }
}

impl MacroDeclaration<()> {
    fn into_concrete<C: crate::CodeStore>(self) -> MacroDeclaration<C> {
        MacroDeclaration {
            docstring: self.docstring,
            seq: self.seq,
            macro_sexp: self.macro_sexp,
            clauses: self
                .clauses
                .into_iter()
                .map(|clause| MacroClause {
                    id: clause.id,
                    params: clause.params,
                    rest_param: clause.rest_param,
                    callable: clause.callable.into_concrete(),
                })
                .collect(),
        }
    }
}

impl Life<()> {
    fn into_concrete<C: crate::CodeStore>(self) -> Life<C> {
        match self {
            Life::Declared { prior } => Life::Declared { prior },
            Life::Template {
                body,
                kind,
                callees,
            } => Life::Template {
                body,
                kind,
                callees,
            },
            Life::Concrete {
                slot,
                realization,
                minted_from,
                ast,
                callees,
                value_use,
                mode_summary,
            } => Life::Concrete {
                slot,
                realization: realization.into_concrete(),
                minted_from,
                ast,
                callees,
                value_use,
                mode_summary,
            },
            Life::Inline { mode_summary } => Life::Inline { mode_summary },
            Life::HostPromised => Life::HostPromised,
            Life::Broken { slot, error } => Life::Broken { slot, error },
        }
    }
}

impl Realization<()> {
    fn into_concrete<C: crate::CodeStore>(self) -> Realization<C> {
        match self {
            Realization::Body { view, code: _ } => Realization::Body { view, code: None },
            Realization::ExternShim { borrowed_sibling } => {
                Realization::ExternShim { borrowed_sibling }
            }
            Realization::Dll => Realization::Dll,
            Realization::FacadeOf { abi_name } => Realization::FacadeOf { abi_name },
        }
    }
}

/// A terminal declaration facet.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[allow(clippy::large_enum_variant)]
pub enum Decl<C: crate::CodeStore = ()> {
    /// A value-level callable governed by the unified lifecycle machine.
    Callable(Callable<C>),
    /// A multi-signature callable whose executable arms are owned by one binding.
    Overloaded(OverloadedCallable<C>),
    /// A macro declaration whose executable clauses are owned by one binding.
    Macro(MacroDeclaration<C>),
    /// An unslotted trait-method declaration used by inference and dispatch.
    TraitMethod(TraitMethodRecord),
    /// A defined or intrinsic type declaration.
    Type(TypeRecord),
    /// A trait declaration.
    Trait(TraitRecord),
    /// A types-authored trait-implementation discovery record.
    ImplShell(ImplShell),
    /// A built-in special form.
    SpecialForm(SpecialFormRecord),
}

/// Unslotted declaration metadata for one method named by a trait.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct TraitMethodRecord {
    /// Method type scheme instantiated by type inference at each reference.
    pub scheme: Scheme,
    /// Method parameter names in declaration order.
    pub param_names: Vec<Symbol>,
    /// Optional user-authored method documentation.
    pub docstring: Option<String>,
    /// Canonical identity of the trait which owns this method.
    pub trait_name: FQTraitName,
}

impl TraitMethodRecord {
    /// Construct an unslotted trait-method dispatch declaration.
    pub fn new(
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        trait_name: FQTraitName,
    ) -> Self {
        Self {
            scheme,
            param_names,
            docstring,
            trait_name,
        }
    }
}

/// One local name exposure of a terminal canonical declaration.
///
/// The record is read-only outside this crate. Consumers author exposures
/// through [`crate::SymbolTable::expose_candidate`] so canonical-source
/// deduplication and visibility dominance remain table-owned.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct NameCandidate {
    /// Terminal canonical storage identity of the exposed declaration.
    pub source: FQSymbol,
    /// Visibility of this exposure in the table that carries it.
    pub visibility: crate::Visibility,
}

impl NameCandidate {
    pub(crate) fn new(source: FQSymbol, visibility: crate::Visibility) -> Self {
        Self { source, visibility }
    }
}

/// Generation-local identity of one executable arm owned by a declaration family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CallableArmId(u32);

impl CallableArmId {
    /// Construct an arm identity from its checked declaration ordinal.
    pub fn from_ordinal(ordinal: usize) -> Result<Self, LifecycleError> {
        u32::try_from(ordinal)
            .map(Self)
            .map_err(|_| LifecycleError::WrongState {
                symbol: Symbol::from(ordinal.to_string()),
                expected: "a callable-arm ordinal representable as u32",
            })
    }

    /// Return the checked declaration ordinal represented by this identity.
    pub fn ordinal(self) -> usize {
        self.0 as usize
    }
}

/// Typed identity of one executable body in a symbol table.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CallableTarget {
    /// A directly named callable binding.
    Binding(FQSymbol),
    /// One arm owned by an overloaded declaration.
    OverloadArm {
        /// Canonical identity of the overloaded declaration.
        owner: FQSymbol,
        /// Generation-local arm identity.
        arm: CallableArmId,
    },
    /// One clause owned by a macro declaration.
    MacroClause {
        /// Canonical identity of the macro declaration.
        owner: FQSymbol,
        /// Generation-local clause identity.
        clause: CallableArmId,
    },
}

/// Scheme, parameters, and lifecycle of one executable callable body.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[non_exhaustive]
pub struct CallableArm<C: crate::CodeStore = ()> {
    /// Authoritative scheme, provisional while declared and settled thereafter.
    pub scheme: Scheme,
    /// Parameter names used by checking, synthesis, and introspection.
    pub param_names: Vec<Symbol>,
    /// Current lifecycle state and the payload legal in that state.
    pub life: Life<C>,
}

impl<C: crate::CodeStore> CallableArm<C> {
    /// Construct an executable arm from its scheme, parameters, and lifecycle.
    pub fn new(scheme: Scheme, param_names: Vec<Symbol>, life: Life<C>) -> Self {
        Self {
            scheme,
            param_names,
            life,
        }
    }
}

/// Slot-free semantic inputs for constructing one freshly settled family arm.
///
/// A draft deliberately cannot carry a callable slot, compiled owner, broken
/// state, or provisional declaration state. [`crate::SymbolTable`] converts
/// the complete draft roster into settled arms while it owns slot allocation.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct CallableArmDraft {
    /// Settled scheme of the family arm.
    pub scheme: Scheme,
    /// Parameter names used by checking, synthesis, and introspection.
    pub param_names: Vec<Symbol>,
    /// Settled body class and the inputs legal for that class.
    pub settlement: CallableArmSettlement,
}

/// Legal fresh-settlement forms accepted by a declaration-family installer.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum CallableArmSettlement {
    /// A non-concrete arm retained as a monomorphisation template.
    Template {
        /// Recipe used to construct concrete instances.
        body: TemplateBody,
        /// Why and how the template is specialized.
        kind: TemplateKind,
        /// Authored callable dependencies, canonicalized at installation.
        callees: Vec<FQSymbol>,
    },
    /// A concrete checked body requiring a table-owned callable slot.
    ConcreteBody {
        /// Checked source body retained for regeneration and introspection.
        ast: DefnVariant,
        /// Fully concrete body consumed by code generation.
        view: MonoDefnVariant,
        /// Authored callable dependencies, canonicalized at installation.
        callees: Vec<FQSymbol>,
    },
}

impl CallableArmDraft {
    /// Construct a slot-free template-arm draft.
    pub fn template(
        scheme: Scheme,
        param_names: Vec<Symbol>,
        body: TemplateBody,
        kind: TemplateKind,
        callees: Vec<FQSymbol>,
    ) -> Self {
        Self {
            scheme,
            param_names,
            settlement: CallableArmSettlement::Template {
                body,
                kind,
                callees,
            },
        }
    }

    /// Construct a slot-free concrete-body draft.
    pub fn concrete_body(
        scheme: Scheme,
        param_names: Vec<Symbol>,
        ast: DefnVariant,
        view: MonoDefnVariant,
        callees: Vec<FQSymbol>,
    ) -> Self {
        Self {
            scheme,
            param_names,
            settlement: CallableArmSettlement::ConcreteBody { ast, view, callees },
        }
    }
}

/// One executable arm owned by an overloaded declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[non_exhaustive]
pub struct OverloadArm<C: crate::CodeStore = ()> {
    /// Generation-local identity equal to this arm's roster position.
    pub id: CallableArmId,
    /// Executable callable state owned by this arm.
    pub callable: CallableArm<C>,
}

/// One authored multi-signature callable declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[non_exhaustive]
pub struct OverloadedCallable<C: crate::CodeStore = ()> {
    /// Optional user-authored documentation for the declaration.
    pub docstring: Option<String>,
    /// Stable declaration order within the owning module.
    pub seq: u64,
    /// Executable arms in checked declaration order.
    pub arms: Vec<OverloadArm<C>>,
}

impl<C: crate::CodeStore> OverloadedCallable<C> {
    /// Construct an overloaded declaration and assign checked ordinal identities.
    pub fn new(
        docstring: Option<String>,
        seq: u64,
        arms: Vec<CallableArm<C>>,
    ) -> Result<Self, LifecycleError> {
        let arms = arms
            .into_iter()
            .enumerate()
            .map(|(ordinal, callable)| {
                Ok(OverloadArm {
                    id: CallableArmId::from_ordinal(ordinal)?,
                    callable,
                })
            })
            .collect::<Result<Vec<_>, LifecycleError>>()?;
        Ok(Self {
            docstring,
            seq,
            arms,
        })
    }
}

/// One executable pattern clause owned by a macro declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[non_exhaustive]
pub struct MacroClause<C: crate::CodeStore = ()> {
    /// Generation-local identity equal to this clause's roster position.
    pub id: CallableArmId,
    /// Fixed positional pattern parameters in source order.
    pub params: Vec<MacroParam>,
    /// Optional rest parameter accepting remaining source forms.
    pub rest_param: Option<Symbol>,
    /// Executable callable state owned by this clause.
    pub callable: CallableArm<C>,
}

/// Slot-free pattern metadata and callable inputs for one fresh macro clause.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct MacroClauseDraft {
    /// Fixed positional pattern parameters in source order.
    pub params: Vec<MacroParam>,
    /// Optional rest parameter accepting remaining source forms.
    pub rest_param: Option<Symbol>,
    /// Slot-free callable inputs for the clause body.
    pub callable: CallableArmDraft,
}

impl MacroClauseDraft {
    /// Construct one slot-free macro-clause draft.
    pub fn new(
        params: Vec<MacroParam>,
        rest_param: Option<Symbol>,
        callable: CallableArmDraft,
    ) -> Self {
        Self {
            params,
            rest_param,
            callable,
        }
    }
}

impl<C: crate::CodeStore> MacroClause<C> {
    /// Construct one macro clause; its declaration validates roster identity.
    pub fn new(
        id: CallableArmId,
        params: Vec<MacroParam>,
        rest_param: Option<Symbol>,
        callable: CallableArm<C>,
    ) -> Self {
        Self {
            id,
            params,
            rest_param,
            callable,
        }
    }
}

/// One authored macro declaration and its ordered executable clauses.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[non_exhaustive]
pub struct MacroDeclaration<C: crate::CodeStore = ()> {
    /// Optional user-authored documentation for the declaration.
    pub docstring: Option<String>,
    /// Stable declaration order within the owning module.
    pub seq: u64,
    /// Original macro form retained for expansion and cache transport.
    pub macro_sexp: Sexp,
    /// Executable clauses in first-match source order.
    pub clauses: Vec<MacroClause<C>>,
}

impl<C: crate::CodeStore> MacroDeclaration<C> {
    /// Construct a macro declaration after validating its complete clause roster.
    pub fn new(
        docstring: Option<String>,
        seq: u64,
        macro_sexp: Sexp,
        clauses: Vec<MacroClause<C>>,
    ) -> Result<Self, LifecycleError> {
        validate_roster_ids(clauses.iter().map(|clause| clause.id))?;
        Ok(Self {
            docstring,
            seq,
            macro_sexp,
            clauses,
        })
    }
}

fn validate_roster_ids(ids: impl IntoIterator<Item = CallableArmId>) -> Result<(), LifecycleError> {
    for (ordinal, id) in ids.into_iter().enumerate() {
        if id != CallableArmId::from_ordinal(ordinal)? {
            return Err(LifecycleError::WrongState {
                symbol: Symbol::from(id.ordinal().to_string()),
                expected: "a unique contiguous callable-arm roster in declaration order",
            });
        }
    }
    Ok(())
}

/// Type-namespace declaration metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TypeRecord {
    /// A user or synthesized algebraic type definition.
    Defined {
        /// Fully resolved type name, parameters, and constructors.
        info: TypeDefInfo,
        /// Optional user-authored documentation.
        docstring: Option<String>,
    },
    /// A compiler-intrinsic type with no ADT constructor roster.
    Intrinsic {
        /// Resolved intrinsic type.
        ty: Type,
        /// Optional built-in documentation.
        docstring: Option<String>,
    },
}

/// Symbol-table facet for a resolved trait declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct TraitRecord {
    /// Resolved trait name, parameters, and method signatures.
    pub info: TraitDeclInfo,
    /// Optional user-authored documentation for the trait.
    pub docstring: Option<String>,
}

impl TraitRecord {
    /// Construct the symbol-table facet for a resolved trait declaration.
    pub fn new(info: TraitDeclInfo, docstring: Option<String>) -> Self {
        Self { info, docstring }
    }
}

/// Discovery shell linking a trait/type pair to its writer module and methods.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ImplShell {
    /// Fully-qualified trait implemented by the shell.
    pub trait_name: FQTraitName,
    /// Fully-qualified receiver type of the implementation.
    pub impl_type: FQTypeName,
    /// Module containing the implementation's callable method entries.
    pub impl_module: crate::ModuleFullPath,
    /// Storage keys of the implementation's method entries.
    pub methods: Vec<Symbol>,
}

/// Introspection metadata for a built-in special form.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct SpecialFormRecord {
    /// The special form's type scheme.
    pub scheme: Scheme,
    /// Names used when displaying the special form's parameters.
    pub param_names: Vec<Symbol>,
    /// Optional user-authored documentation.
    pub docstring: Option<String>,
    /// Built-in usage description shown by introspection.
    pub description: String,
}

impl SpecialFormRecord {
    /// Construct a built-in special-form declaration.
    pub fn new(
        scheme: Scheme,
        param_names: Vec<Symbol>,
        docstring: Option<String>,
        description: String,
    ) -> Self {
        Self {
            scheme,
            param_names,
            docstring,
            description,
        }
    }
}

/// The declaration metadata and lifecycle for one callable binding.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[non_exhaustive]
pub struct Callable<C: crate::CodeStore = ()> {
    /// Optional user-authored documentation.
    pub docstring: Option<String>,
    /// Stable declaration order within the owning module.
    pub seq: u64,
    /// Immutable authorship and semantic role of this callable.
    pub origin: CallableOrigin,
    /// The directly named callable's executable state.
    pub arm: CallableArm<C>,
}

/// The legal states of a callable from declaration through realization.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[allow(clippy::large_enum_variant)]
pub enum Life<C: crate::CodeStore = ()> {
    /// Signature registered but body classification not yet settled.
    Declared {
        /// Displaced slot claim available for same-ABI rebind or retirement.
        prior: Option<CallableSlot>,
    },
    /// Settled non-concrete monomorphisation source with no dispatch slot.
    Template {
        /// Body recipe used to construct concrete instances.
        body: TemplateBody,
        /// Why and how the template is specialized.
        kind: TemplateKind,
        /// Storage identities called by the template body.
        callees: Vec<FQSymbol>,
    },
    /// Settled concrete callable and the only ordinary slot-carrying state.
    Concrete {
        /// Checked module-local GOT capability.
        slot: CallableSlot,
        /// Actor responsible for populating the slot.
        realization: Realization<C>,
        /// Typed template relation for instances; absent on ordinary callables.
        minted_from: Option<InstanceLink>,
        /// Regeneration or introspection source when one exists.
        ast: Option<DefnVariant>,
        /// Storage identities called by this concrete body.
        callees: Vec<FQSymbol>,
        /// Whether the callable is used as a first-class value.
        value_use: bool,
        /// Optional inferred or declared ownership summary.
        mode_summary: Option<ModeSummary>,
    },
    /// Concrete primitive lowered inline at each call site, with no slot.
    Inline {
        /// Optional declared ownership summary used at each lowered call site.
        mode_summary: Option<ModeSummary>,
    },
    /// Concrete host symbol imported by name, with no slot.
    HostPromised,
    /// Failed recompilation retaining its prior slot as a trapping capability.
    Broken {
        /// Retained slot populated with the trap stub.
        slot: CallableSlot,
        /// Provenance of the transaction that broke the binding.
        error: BrokenProvenance,
    },
}

impl<C: crate::CodeStore> Life<C> {
    pub(crate) fn claimed_slot(&self) -> Option<CallableSlot> {
        match self {
            Life::Declared { prior } => *prior,
            Life::Concrete { slot, .. } | Life::Broken { slot, .. } => Some(*slot),
            Life::Template { .. } | Life::Inline { .. } | Life::HostPromised => None,
        }
    }

    fn is_callable_target(&self) -> bool {
        matches!(
            self,
            Life::Concrete { .. } | Life::Inline { .. } | Life::HostPromised | Life::Broken { .. }
        )
    }
}

/// Persisted recipe from which a concrete callable instance can be built.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TemplateBody {
    /// Checked source body reprocessed at concrete arguments.
    Ast(DefnVariant),
    /// Compiler-synthesized constructor or accessor recipe.
    Synth(SynthSpec),
    /// One uniform Rust body served by per-instantiation facades.
    UniformRust {
        /// Linker-visible name of the uniform body.
        abi_name: LinkerSymbol,
    },
}

/// Compiler-synthesized declaration recipe retained by a template.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct SynthSpec {
    /// The declaration-shaped recipe re-synthesized at concrete arguments.
    pub variant: DefnVariant,
}

impl SynthSpec {
    /// Construct a synthesized-body template recipe.
    pub fn new(variant: DefnVariant) -> Self {
        Self { variant }
    }
}

/// Specialization class of a non-concrete callable template.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TemplateKind {
    /// Type variables are pinned by trait obligations.
    Constrained(Box<ConstrainedMeta>),
    /// Type variables are specialized directly without trait dictionaries.
    Parametric,
}

/// Trait obligations attached to a constrained template.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ConstrainedMeta {
    /// Trait obligations indexed by the constrained type variable.
    pub constraints: std::collections::HashMap<crate::TypeId, Vec<FQTraitName>>,
}

impl ConstrainedMeta {
    /// Construct constrained-template metadata from its settled obligations.
    pub fn new(constraints: std::collections::HashMap<crate::TypeId, Vec<FQTraitName>>) -> Self {
        Self { constraints }
    }
}

/// Stable declaration provenance, independent of lifecycle state.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CallableOrigin {
    /// Ordinary single-signature function.
    Plain,
    /// Method body belonging to a discovered trait implementation.
    TraitMethod {
        /// Storage identity of the implementation discovery shell.
        shell: FQSymbol,
        /// Trait whose method this callable implements.
        trait_name: FQTraitName,
        /// Receiver type specialized by the implementation.
        impl_type: FQTypeName,
    },
    /// Synthesized algebraic-data constructor.
    Ctor {
        /// Defined type constructed by this callable.
        type_name: FQTypeName,
        /// Positional runtime constructor tag.
        tag: usize,
        /// Number of payload fields accepted by the constructor.
        field_count: usize,
        /// Whether the constructor is excluded from user exhaustiveness.
        internal: bool,
        /// Product-type facet when type and sole constructor share one key.
        type_def: Option<Box<TypeDefInfo>>,
    },
    /// Synthesized product-field accessor.
    Accessor {
        /// Product type whose field is projected.
        type_name: FQTypeName,
        /// Projected field name.
        field: Symbol,
    },
    /// Hand-written runtime primitive.
    RustPrimitive,
    /// Effect function populated by a platform DLL manifest.
    PlatformEffect {
        /// Scheduling contract declared by the platform descriptor.
        scheduling_class: SchedulingClass,
        /// Whether the ABI entry is a poll-shaped leaf.
        poll_shape: bool,
    },
}

/// The actor responsible for populating a concrete callable's slot.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
#[allow(clippy::large_enum_variant)]
pub enum Realization<C: crate::CodeStore = ()> {
    /// Backend-emitted body whose code pointer is written after compilation.
    Body {
        /// Fully concrete, codegen-ready body.
        view: MonoDefnVariant,
        /// Runtime-only compiled-code owner.
        #[serde(skip)]
        code: Option<C>,
    },
    /// Hand-written Rust extern shim stored into the slot at registration.
    ///
    /// The slot's primary entry follows the uniform consuming convention with
    /// no exception: it takes ownership of every heap argument, releasing it
    /// or moving that same reference into its result, and transfers any heap
    /// result owned. The callable's declared [`ModeSummary`] is an analysis
    /// fact that statically-resolved call sites adapt to; no primary entry
    /// realizes a `Borrowed` parameter or an `IntoResult` flow, and value
    /// wrappers do not adapt to it (`design/arch/ownership-inference.md` §3.1).
    ExternShim {
        /// Optional sibling slot using the borrowed calling convention, chosen
        /// explicitly by statically-resolved call sites and never by a value
        /// wrapper.
        borrowed_sibling: Option<CallableSlot>,
    },
    /// Platform DLL owns and populates the manifest-indexed slot.
    Dll,
    /// Per-instantiation alias over one uniform hand-written body.
    FacadeOf {
        /// Linker-visible name of the shared body.
        abi_name: LinkerSymbol,
    },
}

/// Diagnostic provenance retained when a concrete callable becomes broken.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct BrokenProvenance {
    /// Callable whose failed transaction caused this binding to break.
    pub broken_by: FQSymbol,
    /// Stable diagnostic explaining why the prior slot now traps.
    pub message: String,
}

impl BrokenProvenance {
    /// Construct provenance for a concrete-to-broken lifecycle transition.
    pub fn new(broken_by: FQSymbol, message: String) -> Self {
        Self { broken_by, message }
    }
}

/// A slot that remains permanently unavailable after displacement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct RetiredSlot {
    /// Permanently unavailable module-local slot capability.
    pub slot: CallableSlot,
    /// Transition which retired the slot.
    pub reason: RetireReason,
}

/// Reasons a published callable slot can no longer be rebound.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RetireReason {
    /// Redeclaration settled as a slotless template.
    TemplateFlip {
        /// Binding whose prior slot was retired.
        symbol: Symbol,
    },
    /// Redefinition changed ABI and requires a fresh slot.
    AbiChanging {
        /// Binding whose prior slot was retired.
        symbol: Symbol,
    },
}

/// A symbol-table lifecycle transition or restored-state refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LifecycleError {
    /// A table transaction was proposed for a different module.
    WrongModule {
        /// Module owned by the receiving table.
        expected: crate::ModuleFullPath,
        /// Module carried by the submitted table.
        actual: crate::ModuleFullPath,
    },
    /// A transition named no existing binding.
    MissingBinding {
        /// Missing table key.
        symbol: Symbol,
    },
    /// A transition targeted a non-callable binding.
    NotCallable {
        /// Actual table key.
        symbol: Symbol,
    },
    /// A binding was not in the lifecycle state required by a transition.
    WrongState {
        /// Actual table key.
        symbol: Symbol,
        /// Human-readable required state or table condition.
        expected: &'static str,
    },
    /// Callable origin and lifecycle state form an illegal pairing.
    IllegalOriginState {
        /// Actual table key.
        symbol: Symbol,
    },
    /// Callable origin and state payload describe incompatible realizations.
    IllegalRealization {
        /// Actual table key.
        symbol: Symbol,
    },
    /// A slot-carrying callable has a non-concrete scheme.
    NonConcreteSlot {
        /// Actual table key.
        symbol: Symbol,
    },
    /// A concrete scheme was proposed for a slotless template state.
    ConcreteTemplate {
        /// Actual or proposed table key.
        symbol: Symbol,
    },
    /// Two live claims or tombstones name the same module-local slot.
    DuplicateSlot {
        /// Duplicated slot index.
        slot: usize,
    },
    /// A live claim or tombstone exceeds the fixed GOT slab.
    SlotOutOfRange {
        /// Invalid slot index.
        slot: usize,
    },
    /// A concrete instance was stored under a key not derived from its link.
    InstanceKeyMismatch {
        /// The actual key under which the binding was found or proposed.
        symbol: Symbol,
        /// The canonical key derived from the binding's [`InstanceLink`].
        expected: Symbol,
    },
    /// The checked callable-slot mint refused its scheme or exhausted the slab.
    SlotMint(crate::SlotMintError),
}

impl std::fmt::Display for LifecycleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongModule { expected, actual } => write!(
                f,
                "cannot publish module `{actual}` into module `{expected}`"
            ),
            Self::MissingBinding { symbol } => write!(f, "binding `{symbol}` does not exist"),
            Self::NotCallable { symbol } => write!(f, "binding `{symbol}` is not callable"),
            Self::WrongState { symbol, expected } => {
                write!(f, "binding `{symbol}` is not in {expected} state")
            }
            Self::IllegalOriginState { symbol } => {
                write!(
                    f,
                    "binding `{symbol}` has an illegal callable origin/lifecycle pairing"
                )
            }
            Self::IllegalRealization { symbol } => {
                write!(
                    f,
                    "binding `{symbol}` has an illegal realization for its origin"
                )
            }
            Self::NonConcreteSlot { symbol } => {
                write!(
                    f,
                    "binding `{symbol}` claims a slot for a non-concrete scheme"
                )
            }
            Self::ConcreteTemplate { symbol } => {
                write!(f, "binding `{symbol}` is concrete and cannot be a template")
            }
            Self::DuplicateSlot { slot } => write!(f, "GOT slot {slot} is claimed twice"),
            Self::SlotOutOfRange { slot } => write!(f, "GOT slot {slot} is out of range"),
            Self::InstanceKeyMismatch { symbol, expected } => write!(
                f,
                "instance binding `{symbol}` must be stored under its derived key `{expected}`"
            ),
            Self::SlotMint(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for LifecycleError {}

impl From<crate::SlotMintError> for LifecycleError {
    fn from(error: crate::SlotMintError) -> Self {
        Self::SlotMint(error)
    }
}

/// Structural identity of a concrete instance and its template.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub struct InstanceLink {
    /// Typed identity of the directly named or overloaded template arm.
    pub template: CallableTarget,
    /// Concrete substitutions for the template's generalized variables, ordered
    /// by first occurrence in its scheme type (parameters before result).
    /// Repeated variables occupy one position, including result-only variables.
    pub type_args: Vec<ConcreteType>,
}

impl InstanceLink {
    /// Construct an instance identity from complete generic substitutions.
    /// The caller supplies one type per generalized variable in scheme order
    /// as documented on [`Self::type_args`], not one per value parameter.
    pub fn from_type_args(template: CallableTarget, type_args: Vec<ConcreteType>) -> Self {
        Self {
            template,
            type_args,
        }
    }

    /// Derive identity using the authoritative selected template's scheme.
    ///
    /// The caller must supply the scheme from the intended template generation.
    /// Substitutions follow first structural occurrence among quantified variables;
    /// unused quantifiers take no argument. This projects a signature only: it does
    /// not check constraints or certify that the scheme belongs to the target.
    pub fn instance_key(&self, template_scheme: &Scheme) -> Result<Symbol, InstanceKeyError> {
        let owner = instance_owner(&self.template)?;
        let mut variables = Vec::new();
        crate::collect_var_ids_ordered(&template_scheme.ty, &mut variables);
        variables.retain(|id| template_scheme.type_vars.contains(id));
        if variables.len() != self.type_args.len() {
            return Err(InstanceKeyError::ArgumentCount {
                expected: variables.len(),
                actual: self.type_args.len(),
            });
        }
        let subst = variables
            .into_iter()
            .zip(self.type_args.iter().map(ConcreteType::to_type))
            .collect();
        let ty = crate::apply(&subst, &template_scheme.ty);
        let concrete = ConcreteType::from_type(&ty).map_err(InstanceKeyError::NotConcrete)?;
        concrete_callable_key(owner, &concrete)
    }
}

/// A request to realize one concrete instance of a template.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub struct MonoDemand {
    /// Typed identity of the directly named or overloaded demanded template arm.
    pub template: CallableTarget,
    /// Complete generic substitutions, with the same structural ordering and
    /// one-position-per-variable contract as [`InstanceLink::type_args`].
    pub type_args: Vec<ConcreteType>,
    /// Diagnostic site which requested the instance; excluded from identity.
    pub site: Span,
}

impl MonoDemand {
    /// Request an instance from complete generic substitutions at a diagnostic
    /// site. The caller supplies the vector described by [`Self::type_args`].
    pub fn from_type_args(
        template: CallableTarget,
        type_args: Vec<ConcreteType>,
        site: Span,
    ) -> Self {
        Self {
            template,
            type_args,
            site,
        }
    }

    /// Project the stable template/substitutions identity, excluding the site.
    pub fn instance_link(&self) -> InstanceLink {
        InstanceLink::from_type_args(self.template.clone(), self.type_args.clone())
    }

    /// Derive the canonical storage key shared with [`InstanceLink`].
    pub fn instance_key(&self, template_scheme: &Scheme) -> Result<Symbol, InstanceKeyError> {
        self.instance_link().instance_key(template_scheme)
    }
}

/// A refusal to derive a concrete callable's canonical identity.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum InstanceKeyError {
    /// The substitutions do not match the occurring quantified variables.
    ArgumentCount { expected: usize, actual: usize },
    /// The supplied signature is not a function.
    NotFunction,
    /// A variable or higher-kinded head remains unresolved.
    NotConcrete(crate::NotConcrete),
    /// Macro clauses do not use language-callable instance identity.
    UnsupportedTemplate,
}

impl std::fmt::Display for InstanceKeyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ArgumentCount { expected, actual } => write!(
                f,
                "expected {expected} instance substitutions, got {actual}"
            ),
            Self::NotFunction => f.write_str("instance signature is not a function"),
            Self::NotConcrete(error) => write!(f, "instance signature is not concrete: {error:?}"),
            Self::UnsupportedTemplate => f.write_str("unsupported instance template target"),
        }
    }
}

impl std::error::Error for InstanceKeyError {}

pub(crate) fn instance_owner(target: &CallableTarget) -> Result<&FQSymbol, InstanceKeyError> {
    match target {
        CallableTarget::Binding(owner) | CallableTarget::OverloadArm { owner, .. } => Ok(owner),
        CallableTarget::MacroClause { .. } => Err(InstanceKeyError::UnsupportedTemplate),
    }
}

/// Render semantic executable identity from a canonical authored owner and full
/// concrete function signature. This neither changes authored declaration names
/// nor chooses native object labels. Results participate in identity, including
/// result-only generic specializations. Non-function signatures are refused.
pub fn concrete_callable_key(
    owner: &FQSymbol,
    signature: &ConcreteType,
) -> Result<Symbol, InstanceKeyError> {
    let ConcreteType::Fn(params, result) = signature else {
        return Err(InstanceKeyError::NotFunction);
    };
    Ok(Symbol::from(format!(
        "({owner} [{}] {})",
        render_key_params(params),
        render_key_type(result)
    )))
}

fn render_key_params(params: &[ConcreteType]) -> String {
    params
        .iter()
        .map(render_key_type)
        .collect::<Vec<_>>()
        .join(" ")
}

fn render_key_type(ty: &ConcreteType) -> String {
    crate::render_type(
        &ty.to_type(),
        crate::PrimitiveNaming::Qualified,
        crate::VarNaming::Numbered,
    )
}
