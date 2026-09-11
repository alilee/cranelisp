//! Synthetic-module mount — the int-side reconstruction of the deleted
//! `cranelisp_typecheck::register_builtins` body (FIXME 0242).
//!
//! Synthetic-module assembly left typecheck's bounded context (FIXME 0241,
//! user-arbitrated 2026-05-30): content construction is not type-checking
//! (BC §2). The eight `register_builtins` steps are reconstructed here,
//! building entries **directly** via [`ModuleEntry::def`] (the S73 Tier-1
//! builder) for `Def` entries and plain struct literals + `insert` for the
//! non-`Def` entries (`SpecialForm`, `IntrinsicType`, `TypeDef`). The broader
//! `declare_adt` / `declare_special_form` / `declare_trait` vocabulary stays
//! deferred (FIXME 0241 — minimum mechanism).
//!
//! ## The eight steps (legacy `register_builtins` order)
//!
//! 1. special forms at root `""` (`if`/`let`/`fn`/`defn`/`deftype`/`match`/
//!    `deftrait`/`impl`/`defmacro`/`trace`) as `ModuleEntry::SpecialForm` —
//!    metadata for `/info`. `trace` is a root special form (no import; user
//!    ruling 2026-06-04, FIXME 0266) — only its `Trace`/`TraceCall` ADT lives
//!    in `primitives` (step 7).
//! 2. intrinsic type names in `primitives`: `Int`/`Bool`/`Float`/`String` as
//!    `IntrinsicType`, `Vec` as `TypeDef`.
//! 3. synthetic `macros` module — `SList`/`Sexp` ADTs + `sconcat` primitive.
//! 4. `Option` ADT in `primitives`.
//! 4b. `Pair` ADT in `primitives` (test-discovery.md ruling 1 — `discover-tests`
//!    return shape).
//! 4c. `Result` ADT in `primitives` (test-discovery.md ruling 2 —
//!    `catch-runtime-error` return; tag order Ok=0 / Err=1).
//! 5. `IO` ADT (`Pure`/`Effect`/`Bind`) in `primitives`.
//! 6. `bind` primitive in `primitives`.
//! 7. `Trace` ADT (`TraceCall` + field accessors) in `primitives` (ADT data
//!    declaration only — the 12 runtime bodies live in `cranelisp-intrinsics`,
//!    codegen in backend; see `tracing.md` §2.2 + FIXME 0242 §S76-addendum (4)).
//!    The `trace` *form* metadata is at root `""` (step 1), not here.
//! 8. test-discovery primitives in `primitives`: `discover-tests`
//!    (`DefKind::PrimitiveExtern`, body promised by int at session init) +
//!    `catch-runtime-error` (`DefKind::PrimitiveExtern` post-S83-reshape —
//!    ABI-name `Linkage::Import`, slot-less; body in
//!    `cranelisp-intrinsics::panic`; FIXME 0360). `TestResult`/`run-test` RETIRED
//!    (test-discovery.md, fourth convergence).
//!
//! ## Ordering invariants (legacy body, restated)
//!
//! - `primitives` seeded before special-form metadata reads it (the caller
//!   mounts `PRIMITIVES_TABLE` first; this mount only adds to it).
//! - root `""` exists before special-form registration.
//! - `macros/Sexp` field types resolvable before the first `.cl` parse — the
//!   `macros` module is seeded here, at session init, before any prelude load.
//!
//! ## `next_type_id` threading
//!
//! Each polymorphic ADT (`SList`, `Option`, `IO`) and the polymorphic `bind`
//! primitive allocate fresh `TypeId`s from the session `next_type_id`
//! `AtomicU32` via [`fresh_type_id`]. The high-water mark therefore advances
//! monotonically as the legacy body did (it allocated through
//! `TypeCheckEnv::fresh_var_id`, the same `AtomicU32`).

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};

use cranelisp_types::TypeName;
use cranelisp_types::{
    AdtEntrySpec, Binding, CallableOrigin, CranelispError, Decl, DefnVariant, ErrorLocation, Expr,
    FQSymbol, FQTypeName, ModuleFullPath, Realization, Scheme, Span, SpecialFormRecord, Symbol,
    TemplateBody, TemplateKind, Type, TypeDefInfo, TypeExpr, TypeId, TypeRecord, Visibility,
};

use crate::code::{Code, SessionSymbolTable};

/// A monomorphic scheme — `forall []. ty`. (int-local; typecheck's
/// `crate::scheme::mono` is not part of typecheck's public surface.)
fn mono(ty: Type) -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

/// Allocate the next fresh type variable id from the session counter.
fn fresh_type_id(next_id: &AtomicU32) -> TypeId {
    next_id.fetch_add(1, Ordering::SeqCst)
}

fn bootstrap_error(stage: &str, error: impl std::fmt::Display) -> CranelispError {
    CranelispError::ModuleError {
        message: format!("session bootstrap failed while {stage}: {error}"),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    }
}

fn missing_bootstrap_module(module: &ModuleFullPath, stage: &str) -> CranelispError {
    bootstrap_error(stage, format!("required module `{module}` is absent"))
}

/// `FQTypeName` in the `primitives` module.
fn primitives_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from(name))
}

/// `FQTypeName` in the `macros` module.
fn macros_fqtn(name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("macros"), TypeName::from(name))
}

/// A field of a synthetic constructor with its already-resolved type. The
/// int-side mount constructs FQ field types directly (no `TypeExpr`
/// resolution — synthetic modules have empty imports per Principle 17).
struct SynthField {
    name: &'static str,
    ty: Type,
}

/// A synthetic constructor: name, fields (resolved types), docstring,
/// internal flag. Tag is the positional index in the constructor list.
struct SynthCtor {
    name: &'static str,
    fields: Vec<SynthField>,
    docstring: Option<&'static str>,
    internal: bool,
}

/// Register a synthetic ADT into `module` exactly as the
/// `register_type_def_with_ctor_infos` cascade does (S79 Option 3a, FIXME 0319).
///
/// **R-2 caller wiring (S110 Phase 5, `design/arch/backend-keyed-consumer.md`
/// §6; Principle 24 "Resolve once").** The ordered `(key, entry)` set an ADT
/// registration produces is derived ONCE by
/// [`cranelisp_types::build_adt_entries`] — the single derivation this synthetic
/// seeder shares with typecheck's `deftype` writer
/// (`register_type_def_with_ctor_infos`). Before S110 that shape was maintained
/// as a near-line-for-line MIRROR across the two writers (the audit R-2 finding;
/// the Principle-7 divergent-duplication class). This caller stays thin: it
/// converts its `SynthCtor` input vocabulary into [`cranelisp_types::AdtCtorSpec`]s
/// (pre-allocating each ctor's GOT slot from the session table — slot allocation
/// is table state the pure builder cannot own, allocated in tag order) and
/// inserts every returned pair verbatim. A synthetic module has no §8.6.5
/// contest, so the bare-name `Import` alias pairs the builder returns need no
/// classifier here — unlike typecheck, bootstrap inserts all pairs directly
/// (builder rustdoc §"What the builder owns vs what callers keep").
///
/// The builder handles both facets: **sum/enum** (distinct ctor names —
/// `Option`/`Result`/`IO`) get a separate `ModuleEntry::TypeDef` plus one
/// got-slotted `DefKind::Constructor { type_def: None }` per ctor (bare-name
/// `Import` alias onto the canonical `member_key(Type, Ctor)` `Def`);
/// **single-ctor product** (type-name == sole ctor-name — `Pair`) gets ONE
/// got-slotted ctor `Def` at the bare type-name key carrying the **type facet**
/// (`type_def: Some(..)`), no separate `TypeDef`.
///
/// `type_var_ids` are the (already-allocated) ids quantified in each ctor
/// scheme; the builder derives `Type::ADT(fqtn, [Var(id)…])` from them.
fn register_synth_adt(
    module: &mut SessionSymbolTable,
    fqtn: &FQTypeName,
    type_params: &[&str],
    type_var_ids: &[TypeId],
    adt_docstring: Option<&str>,
    ctors: &[SynthCtor],
) -> Result<(), CranelispError> {
    let type_param_syms: Vec<Symbol> = type_params.iter().map(|p| Symbol::from(*p)).collect();

    // Build the caller-resolved specs. Slot assignment belongs to the table's
    // checked settlement funnel rather than to this synthetic-data adapter.
    let specs: Vec<cranelisp_types::AdtCtorSpec> = ctors
        .iter()
        .map(|c| {
            cranelisp_types::AdtCtorSpec::new(
                Symbol::from(c.name),
                c.fields
                    .iter()
                    .map(|f| cranelisp_types::FieldInfo {
                        name: Symbol::from(f.name),
                        ty: f.ty.clone(),
                    })
                    .collect(),
                c.docstring.map(String::from),
                c.internal,
            )
        })
        .collect();

    let entries = cranelisp_types::build_adt_entries::<Code>(
        fqtn,
        &type_param_syms,
        type_var_ids,
        adt_docstring,
        &specs,
        Visibility::Public,
    );

    // Synthetic modules have no §8.6.5 contest. Settle each returned recipe
    // through the same table-owned lifecycle funnels as source ADTs.
    for (key, entry) in entries {
        match entry {
            AdtEntrySpec::Binding(binding) => {
                module.install_binding(key, binding).map_err(|error| {
                    bootstrap_error("installing a synthetic ADT binding", error)
                })?;
            }
            AdtEntrySpec::Callable(spec) => {
                let bare = matches!(
                    &spec.origin,
                    CallableOrigin::Ctor { type_name, .. }
                        if key.as_ref() != type_name.name.as_ref()
                )
                .then(|| Symbol::from(key.as_ref().rsplit('.').next().unwrap_or(key.as_ref())));
                let variant = spec.synth.variant.clone();
                if spec.scheme.ty.is_concrete() {
                    let view = cranelisp_types::MonoDefnVariant {
                        name: key.clone(),
                        params: spec.param_names.clone(),
                        body: cranelisp_types::MonoExpr::synthetic_local_from_expr(
                            &variant.body,
                            &HashMap::new(),
                        ),
                        span: variant.span,
                        mode_summary: None,
                    };
                    module
                        .install_concrete(
                            key.clone(),
                            spec.scheme,
                            spec.param_names,
                            spec.docstring,
                            0,
                            spec.origin,
                            Realization::Body { view, code: None },
                            Some(variant),
                            Vec::new(),
                            spec.visibility,
                        )
                        .map_err(|error| {
                            bootstrap_error("installing a concrete synthetic ADT member", error)
                        })?;
                } else {
                    module
                        .install_template(
                            key.clone(),
                            spec.scheme,
                            spec.param_names,
                            spec.docstring,
                            0,
                            spec.origin,
                            TemplateBody::Synth(spec.synth),
                            TemplateKind::Parametric,
                            Vec::new(),
                            spec.visibility,
                        )
                        .map_err(|error| {
                            bootstrap_error("installing a generic synthetic ADT member", error)
                        })?;
                }
                if let Some(bare) = bare {
                    module
                        .expose_candidate(
                            bare,
                            FQSymbol {
                                module: fqtn.module.clone(),
                                symbol: key,
                            },
                            Visibility::Public,
                        )
                        .map_err(|error| {
                            bootstrap_error("exposing a synthetic ADT constructor", error)
                        })?;
                }
            }
        }
    }
    Ok(())
}

/// Insert a slot-less `DefKind::PrimitiveExtern` `Def` entry into `module`.
fn insert_primitive(
    module: &mut SessionSymbolTable,
    name: &str,
    scheme: Scheme,
    param_names: Vec<&str>,
    docstring: &str,
) -> Result<(), CranelispError> {
    // These synthetic-module callables (`sconcat`, `quote-sexp`, the Trace field
    // accessors) are seeded slot-less as `DefKind::PrimitiveExtern` — the variant
    // for callees whose body lives outside `cranelisp-primitives` and that
    // dispatch BY-NAME as a `Linkage::Import`, never GOT-indirect (FIXME 0360,
    // ruled S83 /arch Path 1). The backend's builtin-dispatch funnel
    // (`apply.rs`) is slot-agnostic: when `resolve_got_target` finds no slot it
    // falls through to `compile_extern_call` (a by-name `Linkage::Import` the
    // catalog resolves identically in JIT, cache-hit, and `--link`). typecheck's
    // classifier (`infer.rs::resolve_primitive_jit_name`) now accepts
    // `DefKind::PrimitiveExtern` as `BuiltinFn`, so these lower correctly in all
    // three modes (`--run`/REPL/`--link`) with no GOT slot to populate. The
    // interim `Primitive { got_slot }` + dlsym cascade (which broke `--link` —
    // the synthetic `macros` module has no emitted `__cranelisp_got_macros`) is
    // reverted. genuine GOT-slotted primitives (`add-i64`, vec/sexp ops in
    // `cranelisp-primitives`) STAY `Primitive { got_slot }` — unaffected.
    module
        .install_host_promised(
            Symbol::from(name),
            scheme,
            param_names.into_iter().map(Symbol::from).collect(),
            Some(docstring.to_string()),
            0,
            Visibility::Public,
        )
        .map_err(|error| bootstrap_error(format!("installing primitive `{name}`").as_str(), error))
}

/// Mount the synthetic modules into `symbol_tables`. Replaces the deleted
/// `cranelisp_typecheck::register_builtins` (FIXME 0242). The caller has
/// already mounted `user` and `primitives` (via `PRIMITIVES_TABLE`) before
/// this runs.
///
/// **FIXME 0604 census disposition (S115 W6, FIXME 0740): NAMED LEGAL-SKIP of
/// the foreground public-write chokepoint**
/// (`imports.rs::check_exposed_candidate_closure`;
/// `design/int/prelude-table-write-isolation.md` §2.1/§2.4). This runs ONCE at
/// session init, single-threaded, before any worker is spawned — outside the
/// foreground concurrent-compile path — and every entry it seeds is either the
/// module's OWN definition or ONE intra-module public self-alias
/// (`primitives/Bind → primitives/IO.Bind`), both of which the gate admits with
/// no map read. The skip is ASSERTED, not argued:
/// `tests::bootstrap_public_candidate_exposures_are_self_aliases_or_private`
/// sweeps every
/// seeded name candidate through the gate under `D(M) = {}`, so seeding a
/// cross-module PUBLIC exposure here turns that test RED.
pub(crate) fn mount_synthetic_modules(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) -> Result<(), CranelispError> {
    ensure_module(symbol_tables, &ModuleFullPath::from("primitives"));
    ensure_module(symbol_tables, &ModuleFullPath::from(""));

    register_special_forms(symbol_tables)?; // step 1
    register_builtin_type_names(symbol_tables)?; // step 2
    register_macros_module(symbol_tables, next_id)?; // step 3
    register_option_type(symbol_tables, next_id)?; // step 4
    register_pair_type(symbol_tables, next_id)?; // step 4b (test-discovery.md ruling 1)
    register_result_type(symbol_tables, next_id)?; // step 4c (test-discovery.md ruling 1)
    register_io_type(symbol_tables, next_id)?; // step 5
    register_bind_primitive(symbol_tables, next_id)?; // step 6
    register_combinators(symbol_tables, next_id)?; // step 6b (S96 Chunk C, slice 7)
    register_trace_type(symbol_tables)?; // step 7
    register_test_infrastructure(symbol_tables, next_id)?; // step 8
    Ok(())
}

/// The built-in **seeded** modules `/search` treats as importable (spec
/// §17.19 R10, S108). This is the SINGLE source of the seeded-importable list:
/// the Pillar-3 index worker reads it rather than hardcoding module-name
/// literals inside `index_worker` (Principle 19 — bootstrap owns what it
/// mounts). The list is `primitives` + the seeded `macros` module — the two
/// modules `mount_synthetic_modules` seeds with public, importable symbols.
///
/// Deliberately EXCLUDES:
/// - the root `""` module (special-forms-only — `if`/`let`/… are always
///   available and are not importable, so nothing there is a `/search` target);
/// - `prelude` (the implicit outer scope, already skipped by the file-module
///   enumerator, and its symbols are re-exports rather than an importable home).
pub(crate) fn seeded_importable_modules() -> Vec<ModuleFullPath> {
    vec![
        ModuleFullPath::from("primitives"),
        ModuleFullPath::from("macros"),
    ]
}

/// Ensure a module exists in the session table.
fn ensure_module(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    path: &ModuleFullPath,
) {
    if !symbol_tables.contains_key(path) {
        symbol_tables.insert(
            path.clone(),
            SessionSymbolTable::new_with_params(path.clone()),
        );
    }
}

// --- Step 1: special forms (root "") ---

fn register_special_forms(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
) -> Result<(), CranelispError> {
    // Each special form carries its REAL type scheme — the SpecialForm entry is
    // the SINGLE SOURCE for the `:Type` prefix the REPL renders (FIXME 0338, S82
    // W2). The former placeholder `mono(Type::Int)` schemes + the parallel
    // hardcoded `format_special_form_display` `match name { … }` sig table are
    // retired (Principle 7 single-source-of-truth). `if` carries its true
    // `(Fn [Bool a a] a)` shape; the structural forms carry a generic two-arg
    // `(Fn [a a] b)` (a structural macro's argument/return types are not a
    // meaningful monotype — the prefix just signals "form-shaped", consistent
    // with the self-documenting-REPL principle).
    //
    // `(fn [tys] ret)` builder over fresh `Var` ids (ids are display-local — the
    // renderer re-numbers each entry's vars `a`, `b`, … independently).
    let generic = || {
        mono(Type::Fn(
            vec![Type::Var(0), Type::Var(0)],
            Box::new(Type::Var(1)),
        ))
    };
    let if_scheme = mono(Type::Fn(
        vec![Type::Bool, Type::Var(0), Type::Var(0)],
        Box::new(Type::Var(0)),
    ));
    let special_forms: [(&str, Scheme, &str); 9] = [
        ("if", if_scheme, "conditional: (if cond then else)"),
        ("let", generic(), "local binding: (let [x e] body)"),
        ("fn", generic(), "lambda: (fn [params] body)"),
        (
            "defn",
            generic(),
            "function definition: (defn name [params] body)",
        ),
        (
            "deftype",
            generic(),
            "type definition: (deftype Name ctor1 ctor2 ...)",
        ),
        (
            "match",
            generic(),
            "pattern matching: (match expr [pat body] ...)",
        ),
        (
            "deftrait",
            generic(),
            "trait declaration: (deftrait (TraitName a) (method [a ...] ret) ...)",
        ),
        (
            "impl",
            generic(),
            "trait implementation: (impl TraitName Type (method [params] body) ...)",
        ),
        (
            "defmacro",
            generic(),
            "macro definition: (defmacro name [params] body)",
        ),
    ];

    let root_path = ModuleFullPath::from("");
    let mut root = symbol_tables
        .get_mut(&root_path)
        .ok_or_else(|| missing_bootstrap_module(&root_path, "registering special forms"))?;
    for (name, scheme, desc) in special_forms {
        root.install_binding(
            Symbol::from(name),
            Binding::new(
                Decl::SpecialForm(SpecialFormRecord::new(
                    scheme,
                    vec![],
                    Some(desc.to_string()),
                    desc.to_string(),
                )),
                Visibility::Public,
            ),
        )
        .map_err(|error| {
            bootstrap_error(format!("installing special form `{name}`").as_str(), error)
        })?;
    }

    // `trace` is a ROOT special form (user ruling 2026-06-04; tracing.md §3.1,
    // spec §4.12.4): `(trace expr)` is recognised parser-side as `Expr::Trace`
    // and needs NO import — exactly like `if`/`let`. Its SpecialForm metadata
    // (self-documenting-REPL feedback for `/info trace`) therefore lives at root
    // `""`, alongside the other root special forms — NOT in `primitives`. The
    // `Trace`/`TraceCall` ADT names + their accessors STAY in `primitives`
    // (form/ADT asymmetry, spec §3.2.4); only the *form* name `trace` is here.
    // Like the structural forms above, `trace` carries its real `Fn` scheme so
    // the REPL renders a `:Type` prefix from the entry (FIXME 0338).
    let trace_ty = Type::ADT(primitives_fqtn("Trace"), vec![]);
    let trace_form_desc = "Execution trace: (trace expr) — evaluates expr with call instrumentation, returns Trace ADT";
    root.install_binding(
        Symbol::from("trace"),
        Binding::new(
            Decl::SpecialForm(SpecialFormRecord::new(
                mono(Type::Fn(
                    vec![Type::Var(0)], // any expression type
                    Box::new(trace_ty),
                )),
                vec![Symbol::from("expr")],
                Some(trace_form_desc.to_string()),
                trace_form_desc.to_string(),
            )),
            Visibility::Public,
        ),
    )
    .map_err(|error| bootstrap_error("installing special form `trace`", error))?;
    Ok(())
}

// --- Step 2: intrinsic type names (primitives) ---

fn register_builtin_type_names(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
) -> Result<(), CranelispError> {
    let intrinsic_scalars: [(&str, Type, &str); 4] = [
        ("Int", Type::Int, "Machine-word signed integer (spec §3.1)."),
        (
            "Bool",
            Type::Bool,
            "Boolean truth value: true or false (spec §3.1).",
        ),
        (
            "Float",
            Type::Float,
            "Double-precision floating-point number (spec §3.1).",
        ),
        (
            "String",
            Type::String,
            "Immutable UTF-8 text value (spec §3.1).",
        ),
    ];

    let primitives_path = ModuleFullPath::from("primitives");
    let mut primitives = symbol_tables.get_mut(&primitives_path).ok_or_else(|| {
        missing_bootstrap_module(&primitives_path, "registering intrinsic type names")
    })?;

    for (name, ty, desc) in intrinsic_scalars {
        primitives
            .install_binding(
                Symbol::from(name),
                Binding::new(
                    Decl::Type(TypeRecord::Intrinsic {
                        ty,
                        docstring: Some(desc.to_string()),
                    }),
                    Visibility::Public,
                ),
            )
            .map_err(|error| {
                bootstrap_error(
                    format!("installing intrinsic type `{name}`").as_str(),
                    error,
                )
            })?;
    }

    // Vec stays as TypeDef — no Type::Vec variant (vec is Type::ADT(Vec, [elem])).
    // It has no surface constructor, so it is not a product (no type facet).
    primitives
        .install_binding(
            Symbol::from("Vec"),
            Binding::new(
                Decl::Type(TypeRecord::Defined {
                    info: TypeDefInfo {
                        name: primitives_fqtn("Vec"),
                        type_params: vec![],
                        constructors: vec![],
                    },
                    docstring: Some("builtin vector type".to_string()),
                }),
                Visibility::Public,
            ),
        )
        .map_err(|error| bootstrap_error("installing intrinsic type `Vec`", error))?;
    Ok(())
}

// --- Step 3: synthetic `macros` module (SList, Sexp, sconcat) ---

fn register_macros_module(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) -> Result<(), CranelispError> {
    let macros_path = ModuleFullPath::from("macros");
    ensure_module(symbol_tables, &macros_path);

    // Import the intrinsic scalars from primitives into macros so the Sexp
    // field types (bare Int/Bool/Float/String) resolve — Principle 17:
    // synthetic modules have empty imports, so bare-name resolution is
    // import-scoped. (The field types we build below are already FQ Type
    // values, so these imports are belt-and-braces parity with the legacy
    // body — kept so `/info` and qualified-name lookup behave identically.)
    let primitives_path = ModuleFullPath::from("primitives");
    {
        let mut macros = symbol_tables.get_mut(&macros_path).ok_or_else(|| {
            missing_bootstrap_module(&macros_path, "installing macro scalar exposures")
        })?;
        for sym in ["Int", "Bool", "Float", "String"] {
            macros
                .expose_candidate(
                    Symbol::from(sym),
                    FQSymbol {
                        module: primitives_path.clone(),
                        symbol: Symbol::from(sym),
                    },
                    Visibility::Private,
                )
                .map_err(|error| {
                    bootstrap_error(
                        format!("exposing scalar `{sym}` in the macros module").as_str(),
                        error,
                    )
                })?;
        }
    }

    // (SList a): SNil | (SCons [:a shead :(SList a) stail])
    let slist_a = fresh_type_id(next_id);
    let slist_fqtn = macros_fqtn("SList");
    let slist_a_ty = Type::Var(slist_a);
    let slist_self = Type::ADT(slist_fqtn.clone(), vec![slist_a_ty.clone()]);
    {
        let mut macros = symbol_tables
            .get_mut(&macros_path)
            .ok_or_else(|| missing_bootstrap_module(&macros_path, "installing `SList`"))?;
        register_synth_adt(
            &mut macros,
            &slist_fqtn,
            &["a"],
            &[slist_a],
            None,
            &[
                SynthCtor {
                    name: "SNil",
                    fields: vec![],
                    docstring: None,
                    internal: false,
                },
                SynthCtor {
                    name: "SCons",
                    fields: vec![
                        SynthField {
                            name: "shead",
                            ty: slist_a_ty.clone(),
                        },
                        SynthField {
                            name: "stail",
                            ty: slist_self.clone(),
                        },
                    ],
                    docstring: None,
                    internal: false,
                },
            ],
        )?;
    }

    // Sexp: 7 single-field data constructors plus the two-field annotation node.
    let sexp_fqtn = macros_fqtn("Sexp");
    let sexp_ty = Type::ADT(sexp_fqtn.clone(), vec![]);
    let slist_sexp = Type::ADT(slist_fqtn.clone(), vec![sexp_ty.clone()]);
    {
        let mut macros = symbol_tables
            .get_mut(&macros_path)
            .ok_or_else(|| missing_bootstrap_module(&macros_path, "installing `Sexp`"))?;
        register_synth_adt(
            &mut macros,
            &sexp_fqtn,
            &[],
            &[],
            None,
            &[
                sexp_ctor("SexpInt", "sval", Type::Int),
                sexp_ctor("SexpFloat", "sval", Type::Float),
                sexp_ctor("SexpBool", "sval", Type::Bool),
                sexp_ctor("SexpStr", "sval", Type::String),
                sexp_ctor("SexpSym", "sname", Type::String),
                sexp_ctor("SexpList", "sitems", slist_sexp.clone()),
                sexp_ctor("SexpBracket", "sitems", slist_sexp.clone()),
                SynthCtor {
                    name: "SexpAnnotated",
                    fields: vec![
                        SynthField {
                            name: "stype",
                            ty: sexp_ty.clone(),
                        },
                        SynthField {
                            name: "sform",
                            ty: sexp_ty.clone(),
                        },
                    ],
                    docstring: None,
                    internal: false,
                },
            ],
        )?;

        // sconcat :: (Fn [(SList Sexp) (SList Sexp)] (SList Sexp))
        let sconcat_ty = Type::Fn(
            vec![slist_sexp.clone(), slist_sexp.clone()],
            Box::new(slist_sexp.clone()),
        );
        insert_primitive(
            &mut macros,
            "sconcat",
            mono(sconcat_ty),
            vec!["a", "b"],
            "Concatenate two SList Sexp values",
        )?;
    }
    Ok(())
}

fn sexp_ctor(name: &'static str, field: &'static str, ty: Type) -> SynthCtor {
    SynthCtor {
        name,
        fields: vec![SynthField { name: field, ty }],
        docstring: None,
        internal: false,
    }
}

// --- Step 4: Option ADT (primitives) ---

fn register_option_type(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) -> Result<(), CranelispError> {
    let primitives_path = ModuleFullPath::from("primitives");
    let option_a = fresh_type_id(next_id);
    let option_fqtn = primitives_fqtn("Option");
    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .ok_or_else(|| missing_bootstrap_module(&primitives_path, "installing `Option`"))?;
    register_synth_adt(
        &mut primitives,
        &option_fqtn,
        &["a"],
        &[option_a],
        Some("Optional value — None or (Some val)"),
        &[
            SynthCtor {
                name: "None",
                fields: vec![],
                docstring: Some("Absent value"),
                internal: false,
            },
            SynthCtor {
                name: "Some",
                fields: vec![SynthField {
                    name: "val",
                    ty: Type::Var(option_a),
                }],
                docstring: Some("Present value"),
                internal: false,
            },
        ],
    )
}

// --- Step 4b: Pair ADT (primitives) ---

/// Seed `(Pair a b)` with one 2-field data constructor `Pair` into the
/// `primitives` module, modelled on [`register_option_type`].
///
/// `discover-tests` returns `(Vec (Pair String (Fn [] (Option String))))`
/// (test-discovery.md ruling 1) — name + late-bound callable. `Pair` is not
/// otherwise seeded (it lived only in `stdlib/collections/pair.cl`), so it must
/// join the primitives bootstrap seeds. Both fields carry data → heap-allocated
/// (no nullary ctor).
fn register_pair_type(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) -> Result<(), CranelispError> {
    let primitives_path = ModuleFullPath::from("primitives");
    let pair_a = fresh_type_id(next_id);
    let pair_b = fresh_type_id(next_id);
    let pair_fqtn = primitives_fqtn("Pair");
    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .ok_or_else(|| missing_bootstrap_module(&primitives_path, "installing `Pair`"))?;
    register_synth_adt(
        &mut primitives,
        &pair_fqtn,
        &["a", "b"],
        &[pair_a, pair_b],
        Some("Two-field product — (Pair first second)"),
        &[SynthCtor {
            name: "Pair",
            fields: vec![
                SynthField {
                    name: "first",
                    ty: Type::Var(pair_a),
                },
                SynthField {
                    name: "second",
                    ty: Type::Var(pair_b),
                },
            ],
            docstring: Some("Construct a pair"),
            internal: false,
        }],
    )
}

// --- Step 4c: Result ADT (primitives) ---

/// Seed `(Result a b)` with `Ok`/`Err` data constructors into the `primitives`
/// module, modelled on [`register_option_type`].
///
/// `catch-runtime-error :: forall a. (Fn [(Fn [] a)] (Result a String))` returns
/// a `Result` (test-discovery.md ruling 2). Tag order is **Ok=0 / Err=1**
/// (declaration order) — the combinator's marshalling in
/// `cranelisp-intrinsics::panic` assumes this. Both ctors carry one data field →
/// heap-allocated (no nullary ctor).
fn register_result_type(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) -> Result<(), CranelispError> {
    let primitives_path = ModuleFullPath::from("primitives");
    let result_a = fresh_type_id(next_id);
    let result_b = fresh_type_id(next_id);
    let result_fqtn = primitives_fqtn("Result");
    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .ok_or_else(|| missing_bootstrap_module(&primitives_path, "installing `Result`"))?;
    register_synth_adt(
        &mut primitives,
        &result_fqtn,
        &["a", "b"],
        &[result_a, result_b],
        Some("Success or failure — (Ok val) or (Err err)"),
        &[
            SynthCtor {
                name: "Ok",
                fields: vec![SynthField {
                    name: "val",
                    ty: Type::Var(result_a),
                }],
                docstring: Some("Success value"),
                internal: false,
            },
            SynthCtor {
                name: "Err",
                fields: vec![SynthField {
                    name: "err",
                    ty: Type::Var(result_b),
                }],
                docstring: Some("Failure value"),
                internal: false,
            },
        ],
    )
}

// --- Step 5: IO ADT (primitives) ---

fn register_io_type(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) -> Result<(), CranelispError> {
    let primitives_path = ModuleFullPath::from("primitives");
    let io_a = fresh_type_id(next_id);
    let io_fqtn = primitives_fqtn("IO");

    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .ok_or_else(|| missing_bootstrap_module(&primitives_path, "installing `IO`"))?;

    // Pure / Effect via the standard ADT path.
    register_synth_adt(
        &mut primitives,
        &io_fqtn,
        &["a"],
        &[io_a],
        Some("Deferred IO computation tree"),
        &[
            SynthCtor {
                name: "Pure",
                fields: vec![SynthField {
                    name: "ioval",
                    ty: Type::Var(io_a),
                }],
                docstring: Some("Lift a value into IO"),
                internal: false,
            },
            SynthCtor {
                name: "Effect",
                fields: vec![SynthField {
                    name: "thunk",
                    ty: Type::Var(io_a),
                }],
                docstring: Some("Deferred effectful computation"),
                internal: false,
            },
        ],
    )?;

    // Bind (tag=2, internal): existential `b` independent of IO's `a`.
    // HM cannot express the existential, so Bind bypasses the normal ctor
    // scheme path — built manually with two fresh vars, matching the legacy
    // `add_internal_bind_constructor`.
    let bind_a = fresh_type_id(next_id);
    let bind_b = fresh_type_id(next_id);
    let io_b = Type::ADT(io_fqtn.clone(), vec![Type::Var(bind_b)]);
    let io_a_ty = Type::ADT(io_fqtn.clone(), vec![Type::Var(bind_a)]);
    let cont_ty = Type::Fn(vec![Type::Var(bind_b)], Box::new(io_a_ty.clone()));
    let bind_ctor_scheme = Scheme {
        type_vars: vec![bind_a, bind_b],
        constraints: HashMap::new(),
        ty: Type::Fn(
            vec![io_b.clone(), cont_ty.clone()],
            Box::new(Type::ADT(io_fqtn.clone(), vec![Type::Var(bind_a)])),
        ),
    };
    let body_span = Span::SYNTHETIC;
    let bind_param_names = vec![Symbol::from("inner"), Symbol::from("cont")];
    let synth_params: Vec<(Symbol, Option<TypeExpr>)> = bind_param_names
        .iter()
        .cloned()
        .map(|n| (n, None))
        .collect();
    let synth_body = Expr::ConstrADT {
        type_name: io_fqtn.clone(),
        tag: 2,
        fields: bind_param_names
            .iter()
            .map(|n| Expr::Var {
                name: n.clone(),
                span: body_span,
                resolved_call: None,
                inferred_type: None,
            })
            .collect(),
        span: body_span,
        inferred_type: None,
    };

    // Append Bind to IO's constructor list.
    let mut io_info = primitives
        .get("IO")
        .and_then(|binding| binding.type_def_info().cloned())
        .ok_or_else(|| {
            bootstrap_error(
                "extending `IO` with `Bind`",
                "the newly installed `IO` type definition is absent",
            )
        })?;
    io_info.constructors.push(Symbol::from("Bind"));
    primitives
        .install_binding(
            Symbol::from("IO"),
            Binding::new(
                Decl::Type(TypeRecord::Defined {
                    info: io_info,
                    docstring: Some("Deferred IO computation tree".to_string()),
                }),
                Visibility::Public,
            ),
        )
        .map_err(|error| bootstrap_error("extending the `IO` type definition", error))?;
    // Slot rides on the `Constructor` variant (S83 reshape, FIXME 0356/0357).
    // **Uniform canonical keying (S109 W1):** `Bind` is a sum ctor of `IO`, so —
    // like `Pure`/`Effect` and every user `deftype` sum ctor — the real `Def` is
    // keyed `IO.Bind` (`member_key`), the bare `Bind` an `Import` alias onto it;
    // `internal: true` rides the `Def` unchanged.
    let bind_canonical = cranelisp_types::member_key(&io_fqtn.name, "Bind");
    let bind_variant = DefnVariant {
        params: synth_params,
        body: synth_body,
        span: body_span,
    };
    primitives
        .install_template(
            bind_canonical.clone(),
            bind_ctor_scheme,
            bind_param_names,
            Some("Chain IO actions (internal — constructed by bind primitive)".to_string()),
            0,
            CallableOrigin::Ctor {
                type_name: io_fqtn.clone(),
                tag: 2,
                field_count: 2,
                internal: true,
                type_def: None,
            },
            cranelisp_types::TemplateBody::Synth(cranelisp_types::SynthSpec::new(bind_variant)),
            TemplateKind::Parametric,
            Vec::new(),
            Visibility::Public,
        )
        .map_err(|error| bootstrap_error("installing the `IO.Bind` constructor", error))?;
    primitives
        .expose_candidate(
            Symbol::from("Bind"),
            cranelisp_types::FQSymbol {
                module: io_fqtn.module.clone(),
                symbol: bind_canonical,
            },
            Visibility::Public,
        )
        .map_err(|error| bootstrap_error("exposing the `Bind` constructor", error))?;
    Ok(())
}

// --- Step 6: bind primitive (primitives) ---

fn register_bind_primitive(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) -> Result<(), CranelispError> {
    let primitives_path = ModuleFullPath::from("primitives");
    let a = fresh_type_id(next_id);
    let b = fresh_type_id(next_id);
    let io_fqtn = primitives_fqtn("IO");
    let io_a = Type::ADT(io_fqtn.clone(), vec![Type::Var(a)]);
    let io_b = Type::ADT(io_fqtn.clone(), vec![Type::Var(b)]);
    let cont_ty = Type::Fn(vec![Type::Var(a)], Box::new(io_b.clone()));
    let bind_ty = Type::Fn(vec![io_a, cont_ty], Box::new(io_b));
    let bind_scheme = Scheme {
        type_vars: vec![a, b],
        constraints: HashMap::new(),
        ty: bind_ty,
    };

    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .ok_or_else(|| missing_bootstrap_module(&primitives_path, "installing `bind`"))?;
    // `bind` is a slot-less `DefKind::PrimitiveExtern` (FIXME 0360, ruled S83
    // /arch Path 1). It is intercepted inline by backend *by name*
    // (`apply.rs:153`, `op_name == "bind"`) BEFORE any GOT path is reached, so it
    // never touches the GOT and needs no slot. typecheck's classifier
    // (`infer.rs::resolve_primitive_jit_name`) now accepts `PrimitiveExtern` as
    // `BuiltinFn`, so `bind` resolves as a builtin in all three modes. The
    // interim `Primitive { got_slot }` + dlsym cascade is reverted (it serviced a
    // slot that is never read and broke `--link` for the sibling synthetic
    // externs).
    insert_primitive(
        &mut primitives,
        "bind",
        bind_scheme,
        vec!["io", "f"],
        "Chain IO actions: extract value from first IO, pass to continuation",
    )
}

// --- Step 6b: race/select combinators (primitives) ---
//
// The user-facing control combinators (S96 Chunk C, slice 7; spec §10.12.8,
// design `io-trampoline.md §16` / `reactor.md §2.15`). Like `bind`, both are
// slot-less `DefKind::PrimitiveExtern` entries: typecheck's classifier
// (`resolve_primitive_jit_name`) accepts `PrimitiveExtern` as
// `ResolvedCall::BuiltinFn { name }`, and the backend name-matches `race`/`select`
// at its `BuiltinFn` apply-dispatch arm (`apply.rs`, the `bind` precedent) — NO
// inferred AST marker (`io-trampoline.md §16.2`). They never touch the GOT, so
// they need no slot.
//
// `timeout` is deliberately NOT seeded here — it is a derived `.cl` stdlib
// composition (`timeout d io = race io (sleep d)`, §2.18) owned by the C4 wave;
// seeding it as a builtin would duplicate that derivation.
fn register_combinators(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) -> Result<(), CranelispError> {
    let primitives_path = ModuleFullPath::from("primitives");
    let io_fqtn = primitives_fqtn("IO");
    let vec_fqtn = primitives_fqtn("Vec");

    // race : forall a. IO a -> IO a -> IO a — the binary first-to-complete race.
    let ra = fresh_type_id(next_id);
    let io_ra = Type::ADT(io_fqtn.clone(), vec![Type::Var(ra)]);
    let race_ty = Type::Fn(vec![io_ra.clone(), io_ra.clone()], Box::new(io_ra.clone()));
    let race_scheme = Scheme {
        type_vars: vec![ra],
        constraints: HashMap::new(),
        ty: race_ty,
    };

    // select : forall a. Vec (IO a) -> IO a — the n-ary generalisation over a
    // branch list (the `[..]` literal is a `Vec`); returns the winner's value.
    let sa = fresh_type_id(next_id);
    let io_sa = Type::ADT(io_fqtn, vec![Type::Var(sa)]);
    let vec_io_sa = Type::ADT(vec_fqtn, vec![io_sa.clone()]);
    let select_ty = Type::Fn(vec![vec_io_sa], Box::new(io_sa));
    let select_scheme = Scheme {
        type_vars: vec![sa],
        constraints: HashMap::new(),
        ty: select_ty,
    };

    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .ok_or_else(|| missing_bootstrap_module(&primitives_path, "installing IO combinators"))?;
    insert_primitive(
        &mut primitives,
        "race",
        race_scheme,
        vec!["a", "b"],
        "Race two IO actions: the first to complete wins; the loser is cancelled",
    )?;
    insert_primitive(
        &mut primitives,
        "select",
        select_scheme,
        vec!["branches"],
        "Race a list of IO actions: the first to complete wins; the losers are cancelled",
    )?;

    // sleep : Int -> IO Int — the runtime timer poll leaf (S96 Chunk C4, slice 7;
    // spec §10.12.8, `reactor.md §2.18`). `(sleep d)` arms the reactor's timer and
    // resumes (with `0`) after `d` MILLISECONDS. Like `race`/`select`/`bind` it is a
    // slot-less `DefKind::PrimitiveExtern` name-matched at the backend's `BuiltinFn`
    // apply arm (`compile_sleep`, the non-GOT runtime-symbol `code_ptr` path) — it
    // never touches the GOT. Monomorphic (no type vars): the result inner type is
    // `Int` (the language has no `Unit` type; `0` is the discarded result). It is the
    // one leaf the derived `timeout = race (map-io Some io) (map-io (fn [_] None)
    // (sleep d))` stdlib composition builds on.
    let sleep_ty = Type::Fn(
        vec![Type::Int],
        Box::new(Type::ADT(primitives_fqtn("IO"), vec![Type::Int])),
    );
    let sleep_scheme = Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty: sleep_ty,
    };
    insert_primitive(
        &mut primitives,
        "sleep",
        sleep_scheme,
        vec!["d"],
        "Sleep for d milliseconds (a timer IO leaf): arms the reactor timer and resumes after the delay",
    )?;
    Ok(())
}

// --- Step 7: Trace ADT + field accessors + `trace` form (primitives) ---

fn register_trace_type(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
) -> Result<(), CranelispError> {
    let primitives_path = ModuleFullPath::from("primitives");
    let trace_fqtn = primitives_fqtn("Trace");
    let trace_ty = Type::ADT(trace_fqtn.clone(), vec![]);
    let slist_string = Type::ADT(macros_fqtn("SList"), vec![Type::String]);
    let slist_trace = Type::ADT(macros_fqtn("SList"), vec![trace_ty.clone()]);

    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .ok_or_else(|| missing_bootstrap_module(&primitives_path, "installing `Trace`"))?;

    register_synth_adt(
        &mut primitives,
        &trace_fqtn,
        &[],
        &[],
        Some("Recorded execution call tree from (trace expr)"),
        &[SynthCtor {
            name: "TraceCall",
            fields: vec![
                SynthField {
                    name: "name",
                    ty: Type::String,
                },
                SynthField {
                    name: "params",
                    ty: slist_string.clone(),
                },
                SynthField {
                    name: "result",
                    ty: Type::String,
                },
                SynthField {
                    name: "children",
                    ty: slist_trace.clone(),
                },
                SynthField {
                    name: "nanos",
                    ty: Type::Int,
                },
            ],
            docstring: Some("Trace call tree node"),
            internal: false,
        }],
    )?;

    // Field accessor functions (monomorphic Defs): (Fn [Trace] FieldTy).
    let accessors: [(&str, &str, Type); 5] = [
        (
            "name",
            "Fully qualified function name from trace call",
            Type::String,
        ),
        (
            "params",
            "Formatted parameter values from trace call",
            slist_string,
        ),
        (
            "result",
            "Formatted result value from trace call",
            Type::String,
        ),
        ("children", "Child calls in trace node", slist_trace),
        ("nanos", "Wall-clock nanoseconds for trace call", Type::Int),
    ];
    for (field_name, docstring, return_ty) in accessors {
        let scheme = mono(Type::Fn(vec![trace_ty.clone()], Box::new(return_ty)));
        insert_primitive(&mut primitives, field_name, scheme, vec!["t"], docstring)?;
    }

    // NOTE: the `trace` SpecialForm metadata entry is registered at ROOT `""`
    // (see `register_special_forms`, step 1), NOT here — `trace` is a root
    // special form needing no import (user ruling 2026-06-04; FIXME 0266
    // resolved). Only the `Trace`/`TraceCall` ADT + accessors live in
    // `primitives` (form/ADT asymmetry, spec §3.2.4).
    Ok(())
}

// --- Step 8: test-discovery primitives (primitives) ---
//
// test-discovery.md (fourth convergence, SETTLED): `TestResult`/`run-test`
// RETIRE; `discover-tests` becomes a `DefKind::PrimitiveExtern` returning
// fn-value pairs; `catch-runtime-error` is a standalone `DefKind::PrimitiveExtern`
// combinator (S83 reshape, FIXME 0360 — slot-less ABI-name dispatch) backed by
// the `cranelisp-intrinsics::panic` C-ABI export.

fn register_test_infrastructure(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) -> Result<(), CranelispError> {
    let primitives_path = ModuleFullPath::from("primitives");
    let mut primitives = symbol_tables.get_mut(&primitives_path).ok_or_else(|| {
        missing_bootstrap_module(&primitives_path, "installing test infrastructure")
    })?;

    // The eligible-test callable: `(Fn [] (Option String))` — None=pass,
    // (Some reason)=fail. The wrapper's own type and the eligibility filter
    // are the same contract (q-eligibility).
    let option_string = Type::ADT(primitives_fqtn("Option"), vec![Type::String]);
    let test_callable = Type::Fn(vec![], Box::new(option_string));
    // (Pair String (Fn [] (Option String)))
    let pair_name_callable = Type::ADT(primitives_fqtn("Pair"), vec![Type::String, test_callable]);
    // (Vec (Pair ...)) — return; (Vec String) — argument (module paths).
    let vec_pairs = Type::ADT(primitives_fqtn("Vec"), vec![pair_name_callable]);
    let vec_string = Type::ADT(primitives_fqtn("Vec"), vec![Type::String]);

    // discover-tests :: (Fn [(Vec String)] (Vec (Pair String (Fn [] (Option String)))))
    //
    // DefKind::PrimitiveExtern — body promised by int at session init via
    // `Jit::define_symbol("discover-tests", discover_tests_extern)`. No GOT
    // slot, no code; backend lowers a call as Linkage::Import against the key.
    // The no-arg and single-String shapes are stdlib-macro sugar normalising
    // to the `(Vec String)` form (FIXME 0273, /stdlib).
    insert_primitive(
        &mut primitives,
        "discover-tests",
        mono(Type::Fn(vec![vec_string], Box::new(vec_pairs))),
        vec!["modules"],
        "Discover eligible test-* functions across the given module paths: \
         returns (Vec (Pair name late-bound-callable)).",
    )?;

    // catch-runtime-error :: forall a. (Fn [(Fn [] a)] (Result a String))
    //
    // A plain forall scheme with EMPTY constraints (modelled on
    // `register_bind_primitive`) — one runtime body serves every `a` (uniform
    // i64 ABI), so the constrained-fn monomorphisation machinery is NOT
    // engaged. JIT name = ABI name = "catch-runtime-error" — resolved from the
    // intrinsics archive (intrinsics_table() entry); no `define_symbol`.
    let a = fresh_type_id(next_id);
    let thunk_ty = Type::Fn(vec![], Box::new(Type::Var(a)));
    let result_a_string = Type::ADT(primitives_fqtn("Result"), vec![Type::Var(a), Type::String]);
    let cre_scheme = Scheme {
        type_vars: vec![a],
        constraints: HashMap::new(),
        ty: Type::Fn(vec![thunk_ty], Box::new(result_a_string)),
    };
    // `catch-runtime-error`'s body is `cranelisp_intrinsics::panic`, resolved
    // by ABI name (JIT symbol fallback / cache Linker register / `cc` archive
    // link in `--link`) — slot-less, never GOT-indirect. Under the S83 reshape
    // a slot-bearing `Primitive` lowered its call GOT-indirect through a slot
    // that no mode populates (SIGSEGV, observed in `--run` AND `--link`);
    // `PrimitiveExtern` restores the by-name `Linkage::Import` lowering in all
    // modes (FIXME 0360).
    insert_primitive(
        &mut primitives,
        "catch-runtime-error",
        cre_scheme,
        vec!["thunk"],
        "Invoke a thunk under runtime-error protection: returns \
         (Ok result) on success or (Err message) on a runtime panic.",
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{CallableOrigin, Life, TemplateBody};

    /// Test helper: resolve a constructor by its BARE name to the terminal `Def`,
    /// following the S109 same-module bare→canonical `Import` alias one hop (a sum
    /// ctor's real `Def` is keyed `Type.Ctor` via `member_key`). Type-agnostic.
    fn ctor_entry<'t>(
        table: &'t SessionSymbolTable,
        name: &str,
    ) -> Option<&'t Binding<crate::code::Code>> {
        if let Some(binding) = table.get(name) {
            return Some(binding);
        }
        let candidates = table.name_candidates(&Symbol::from(name));
        let [candidate] = candidates.as_slice() else {
            return None;
        };
        table.get(candidate.source.symbol.as_ref())
    }

    fn fresh_tables() -> (
        dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
        AtomicU32,
    ) {
        let tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable> = dashmap::DashMap::new();
        tables.insert(
            ModuleFullPath::from("user"),
            SessionSymbolTable::new_with_params(ModuleFullPath::from("user")),
        );
        tables.insert(
            ModuleFullPath::from("primitives"),
            SessionSymbolTable::new_with_params(ModuleFullPath::from("primitives")),
        );
        (tables, AtomicU32::new(0))
    }

    // spec: design/int/int.md "S121 correction" — session
    // bootstrap is a typed error boundary. A lifecycle refusal while installing
    // a synthetic seed must return a located compiler error, never unwind.
    #[test]
    fn bootstrap_lifecycle_conflict_returns_error_without_unwind() {
        let (tables, next_id) = fresh_tables();
        let root_path = ModuleFullPath::from("");
        ensure_module(&tables, &root_path);
        tables
            .get_mut(&root_path)
            .expect("root fixture exists")
            .install_host_promised(
                Symbol::from("if"),
                mono(Type::Fn(vec![Type::Int], Box::new(Type::Int))),
                vec![Symbol::from("x")],
                Some("incompatible bootstrap fixture".to_string()),
                0,
                Visibility::Public,
            )
            .expect("conflicting fixture installs");

        let attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            mount_synthetic_modules(&tables, &next_id)
        }));
        let error = attempt
            .expect("bootstrap lifecycle refusal must not unwind")
            .expect_err("incompatible pre-existing `if` binding must be refused");
        assert!(
            matches!(error, CranelispError::ModuleError { .. }),
            "bootstrap refusal uses the existing located compiler-error vocabulary: {error:?}"
        );
        assert_eq!(error.span(), Span::SYNTHETIC);
        assert!(
            error.message().contains("session bootstrap failed")
                && error.message().contains("special form `if`"),
            "bootstrap context identifies the failed seed: {error:?}"
        );
    }

    // spec: design/int/prelude-table-write-isolation.md §2.1/§2.4 (FIXME 0604
    // census; 0740 disposition) — `mount_synthetic_modules` is a NAMED LEGAL-SKIP
    // of the foreground public-write chokepoint, and this is its DETECTION PROOF
    // rather than an argument. Every candidate exposure the bootstrap seeds is
    // swept through `check_exposed_candidate_closure` with the STRICTEST possible
    // declared-export closure — `D(M) = {}` — so the unknown-D permit arm cannot
    // mask anything. A future cross-module PUBLIC candidate — the phantom shape
    // the gate exists to reject — turns this test RED.
    #[test]
    fn bootstrap_public_candidate_exposures_are_self_aliases_or_private() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let empty: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
        let mut checked = 0usize;
        for module in tables.iter() {
            let path = module.key().clone();
            for (name, exposure) in module.value().all_name_candidates() {
                if exposure.visibility == Visibility::Public {
                    assert_eq!(
                        exposure.source.module, path,
                        "bootstrap public candidate `{name}` must be a same-module self-alias"
                    );
                }
                crate::imports::check_exposed_candidate_closure(
                    &path,
                    name,
                    &exposure.source,
                    exposure.visibility,
                    cranelisp_types::Span::SYNTHETIC,
                    Some(&empty),
                )
                .unwrap_or_else(|e| {
                    panic!(
                        "bootstrap candidate `{name}` in module `{path}` is not a legal \
                         skip of the 0604 chokepoint: {e:?}"
                    )
                });
                checked += 1;
            }
        }
        assert!(
            checked > 5,
            "the sweep must actually see seeded candidates; checked {checked}"
        );

        let planted = crate::imports::check_exposed_candidate_closure(
            &ModuleFullPath::from("macros"),
            &Symbol::from("foreign"),
            &FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("foreign"),
            },
            Visibility::Public,
            Span::SYNTHETIC,
            Some(&empty),
        );
        assert!(
            planted.is_err(),
            "a planted public cross-module candidate outside D(M) must be rejected"
        );
    }

    #[test]
    fn mounts_special_forms_at_root() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let root = tables.get(&ModuleFullPath::from("")).unwrap();
        assert!(matches!(
            root.get("if"),
            Some(Binding {
                declaration: Decl::SpecialForm(_),
                ..
            })
        ));
        assert!(matches!(
            root.get("defmacro"),
            Some(Binding {
                declaration: Decl::SpecialForm(_),
                ..
            })
        ));
    }

    #[test]
    fn mounts_intrinsic_scalars_in_primitives() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        assert!(matches!(
            prims.get("Int"),
            Some(Binding {
                declaration: Decl::Type(TypeRecord::Intrinsic { ty: Type::Int, .. }),
                ..
            })
        ));
        assert!(matches!(
            prims.get("Vec"),
            Some(Binding {
                declaration: Decl::Type(TypeRecord::Defined { .. }),
                ..
            })
        ));
    }

    #[test]
    fn mounts_macros_sexp_and_slist() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let macros = tables.get(&ModuleFullPath::from("macros")).unwrap();
        assert!(matches!(
            macros.get("Sexp"),
            Some(Binding {
                declaration: Decl::Type(TypeRecord::Defined { .. }),
                ..
            })
        ));
        assert!(matches!(
            macros.get("SList"),
            Some(Binding {
                declaration: Decl::Type(TypeRecord::Defined { .. }),
                ..
            })
        ));
        // SCons is a data constructor Def.
        assert!(matches!(
            ctor_entry(&macros, "SCons"),
            Some(Binding { declaration: Decl::Callable(callable), .. })
                if matches!(callable.origin, CallableOrigin::Ctor { .. })
        ));
        assert!(matches!(
            macros.get("sconcat"),
            Some(Binding {
                declaration: Decl::Callable(_),
                ..
            })
        ));
        // spec: spec/09-macros.md §9.1.2 — reader-folded annotations are
        // available to macro code as (SexpAnnotated stype sform), tag 7.
        match ctor_entry(&macros, "SexpAnnotated") {
            Some(Binding {
                declaration: Decl::Callable(callable),
                ..
            }) => {
                assert!(matches!(
                    callable.origin,
                    CallableOrigin::Ctor {
                        tag: 7,
                        field_count: 2,
                        ..
                    }
                ));
                assert_eq!(
                    &callable.arm.param_names,
                    &vec![Symbol::from("stype"), Symbol::from("sform")]
                );
                assert_eq!(
                    callable.arm.scheme.ty,
                    Type::Fn(
                        vec![
                            Type::ADT(macros_fqtn("Sexp"), vec![]),
                            Type::ADT(macros_fqtn("Sexp"), vec![]),
                        ],
                        Box::new(Type::ADT(macros_fqtn("Sexp"), vec![])),
                    )
                );
            }
            other => panic!("SexpAnnotated should be a two-field constructor, got {other:?}"),
        }
    }

    #[test]
    fn mounts_option_io_bind() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        assert!(matches!(
            prims.get("Option"),
            Some(Binding {
                declaration: Decl::Type(TypeRecord::Defined { .. }),
                ..
            })
        ));
        assert!(matches!(
            ctor_entry(&prims, "Some"),
            Some(Binding {
                declaration: Decl::Callable(_),
                ..
            })
        ));
        assert!(matches!(
            prims.get("IO"),
            Some(Binding {
                declaration: Decl::Type(TypeRecord::Defined { .. }),
                ..
            })
        ));
        assert!(matches!(
            prims.get("bind"),
            Some(Binding {
                declaration: Decl::Callable(_),
                ..
            })
        ));
        // Bind is internal.
        match ctor_entry(&prims, "Bind") {
            Some(Binding {
                declaration: Decl::Callable(callable),
                ..
            }) => match &callable.origin {
                CallableOrigin::Ctor { internal, tag, .. } => {
                    assert!(*internal);
                    assert_eq!(*tag, 2);
                }
                _ => panic!("Bind should be a constructor callable"),
            },
            _ => panic!("Bind should be a Def"),
        }
        // IO has 3 constructors recorded.
        if let Some(Binding {
            declaration: Decl::Type(TypeRecord::Defined { info, .. }),
            ..
        }) = prims.get("IO")
        {
            assert_eq!(info.constructors.len(), 3);
        }
    }

    // S96 Chunk C, slice 7 — `race`/`select` are seeded as slot-less
    // `DefKind::PrimitiveExtern` entries in `primitives` (so typecheck resolves
    // them to `BuiltinFn` and the backend name-matches them, the `bind` precedent),
    // public, with their §10.12.8 schemes. `timeout` is deliberately NOT seeded (a
    // C4 stdlib derivation). RED on revert: without `register_combinators` the
    // entries are absent.
    #[test]
    fn mounts_race_select_combinators() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();

        // race : IO a -> IO a -> IO a — slot-less PrimitiveExtern, public, binary.
        match prims.get("race") {
            Some(Binding {
                declaration: Decl::Callable(callable),
                visibility,
                ..
            }) => {
                assert!(matches!(callable.arm.life, Life::HostPromised));
                assert_eq!(*visibility, Visibility::Public);
                match &callable.arm.scheme.ty {
                    Type::Fn(params, _) => assert_eq!(params.len(), 2, "race is binary"),
                    other => panic!("race must be a Fn type, got {other:?}"),
                }
            }
            other => panic!("race must be a PrimitiveExtern Def, got {other:?}"),
        }

        // select : Vec (IO a) -> IO a — slot-less PrimitiveExtern, public, unary.
        match prims.get("select") {
            Some(Binding {
                declaration: Decl::Callable(callable),
                visibility,
                ..
            }) => {
                assert!(matches!(callable.arm.life, Life::HostPromised));
                assert_eq!(*visibility, Visibility::Public);
                match &callable.arm.scheme.ty {
                    Type::Fn(params, _) => {
                        assert_eq!(params.len(), 1, "select takes one branch list")
                    }
                    other => panic!("select must be a Fn type, got {other:?}"),
                }
            }
            other => panic!("select must be a PrimitiveExtern Def, got {other:?}"),
        }

        // `timeout` is a C4 stdlib derivation, NOT a seeded builtin.
        assert!(
            prims.get("timeout").is_none(),
            "timeout must NOT be a seeded builtin (C4 stdlib)"
        );
    }

    #[test]
    fn mounts_trace_and_test_infrastructure() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        assert!(matches!(
            prims.get("Trace"),
            Some(Binding {
                declaration: Decl::Type(TypeRecord::Defined { .. }),
                ..
            })
        ));
        // FIXME 0266 RESOLVED (user ruling 2026-06-04): `trace` is a ROOT
        // special form needing no import; its SpecialForm metadata lives at
        // root `""`, NOT in `primitives`. The `Trace`/`TraceCall` ADT + its
        // accessors stay in `primitives` (form/ADT asymmetry, spec §3.2.4).
        assert!(
            prims.get("trace").is_none(),
            "trace form must NOT be in primitives (it is a root special form)"
        );
        let root = tables.get(&ModuleFullPath::from("")).unwrap();
        assert!(
            matches!(
                root.get("trace"),
                Some(Binding {
                    declaration: Decl::SpecialForm(_),
                    ..
                })
            ),
            "trace SpecialForm metadata must resolve at root \"\""
        );
        // TestResult / run-test RETIRED (test-discovery.md, fourth convergence).
        assert!(
            prims.get("TestResult").is_none(),
            "TestResult must be retired"
        );
        assert!(prims.get("run-test").is_none(), "run-test must be retired");
        // discover-tests is now a PrimitiveExtern (host-promised body).
        assert!(matches!(
            prims.get("discover-tests"),
            Some(entry @ Binding { declaration: Decl::Callable(callable), .. })
                if matches!(callable.arm.life, Life::HostPromised)
                    && entry.callable_got_slot().is_none()
        ));
    }

    #[test]
    fn mounts_pair_and_result_in_primitives() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        // `Pair` is a same-name single-ctor **product** type (S79 Option 3a,
        // FIXME 0319): the type and its sole 2-field constructor share the name,
        // so the surviving `"Pair"` entry is the got-slotted ctor `Def` carrying
        // a **type facet** (`type_def: Some(..)`) — NOT a `TypeDef`. The ctor
        // scheme `(Fn [a b] (Pair a b))` lives on the `Def`'s own `scheme`, its
        // field names on `param_names`. Without this, `(Pair 1 2)`,
        // `(match _ [(Pair a b) …])` and `Pair` as a first-class value are
        // unresolvable. Assert the dual facet, not just the name's existence.
        match prims.get("Pair") {
            Some(Binding {
                declaration: Decl::Callable(callable),
                ..
            }) => {
                match &callable.origin {
                    CallableOrigin::Ctor {
                        type_def: Some(td),
                        field_count,
                        ..
                    } => {
                        assert_eq!(
                            td.constructors,
                            vec![Symbol::from("Pair")],
                            "Pair's type facet lists its sole ctor"
                        );
                        assert_eq!(*field_count, 2, "Pair constructor takes 2 fields");
                    }
                    other => panic!(
                        "Pair (product) must be DefKind::Constructor with type_def: Some, got {other:?}"
                    ),
                }
                assert_eq!(
                    &callable.arm.param_names,
                    &vec![Symbol::from("first"), Symbol::from("second")],
                    "Pair field names ride on the ctor Def's param_names"
                );
                match &callable.arm.scheme.ty {
                    Type::Fn(fields, ret) => {
                        assert_eq!(fields.len(), 2, "Pair constructor takes 2 fields");
                        assert!(
                            matches!(ret.as_ref(), Type::ADT(name, _) if name.to_string().ends_with("Pair")),
                            "Pair constructor returns the Pair ADT, got {ret:?}"
                        );
                    }
                    other => panic!("Pair ctor scheme must be a Fn type, got {other:?}"),
                }
            }
            other => panic!("Pair should be a got-slotted ctor Def, got {other:?}"),
        }
        assert!(matches!(
            prims.get("Result"),
            Some(Binding {
                declaration: Decl::Type(TypeRecord::Defined { .. }),
                ..
            })
        ));
        // Ok=tag 0, Err=tag 1 (declaration order — the combinator assumes this).
        match ctor_entry(&prims, "Ok") {
            Some(Binding {
                declaration: Decl::Callable(callable),
                ..
            }) => match &callable.origin {
                CallableOrigin::Ctor {
                    tag, field_count, ..
                } => {
                    assert_eq!(*tag, 0);
                    assert_eq!(*field_count, 1);
                }
                _ => panic!("Ok should be a Constructor"),
            },
            other => panic!("Ok should be a Def, got {other:?}"),
        }
        match ctor_entry(&prims, "Err") {
            Some(Binding {
                declaration: Decl::Callable(callable),
                ..
            }) => match &callable.origin {
                CallableOrigin::Ctor { tag, .. } => assert_eq!(*tag, 1),
                _ => panic!("Err should be a Constructor"),
            },
            other => panic!("Err should be a Def, got {other:?}"),
        }
    }

    #[test]
    fn mounts_catch_runtime_error_primitive() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        match prims.get("catch-runtime-error") {
            Some(
                entry @ Binding {
                    declaration: Decl::Callable(callable),
                    ..
                },
            ) => {
                // S83 Wave-1 reshape (FIXME 0360): `catch-runtime-error` is
                // dispatched by ABI name as a `Linkage::Import` (body
                // `cranelisp_intrinsics::panic`), never GOT-indirect. It is
                // therefore a SLOT-LESS `DefKind::PrimitiveExtern`, not a
                // slot-bearing `DefKind::Primitive` (which post-reshape would
                // lower the call through an unpopulated GOT slot → SIGSEGV).
                assert!(matches!(callable.arm.life, Life::HostPromised));
                assert!(
                    entry.callable_got_slot().is_none(),
                    "an ABI-name-dispatched extern carries no GOT slot"
                );
                // forall a. (Fn [(Fn [] a)] (Result a String)) — one quantified
                // var, empty constraints (plain forall, not constrained-fn).
                assert_eq!(callable.arm.scheme.type_vars.len(), 1);
                assert!(callable.arm.scheme.constraints.is_empty());
            }
            other => panic!("catch-runtime-error should be a PrimitiveExtern Def, got {other:?}"),
        }
    }

    // spec: design/arch/concreteness-types-first.md §1.3 — enumerate the
    // production bootstrap's complete generic uniform-body roster through the
    // lifecycle carriers that actually mount it.
    #[test]
    fn bootstrap_generic_uniform_body_roster_is_closed() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        let mut roster = std::collections::BTreeSet::new();
        for module in tables.iter() {
            for (name, binding) in module.value().all_symbols() {
                let Some(callable) = binding.callable() else {
                    continue;
                };
                if callable.arm.scheme.type_vars.is_empty() {
                    continue;
                }
                let body = match &callable.arm.life {
                    Life::HostPromised => Some("HostPromised".to_string()),
                    Life::Template {
                        body: TemplateBody::UniformRust { abi_name },
                        ..
                    } => Some(format!("UniformRust({abi_name})")),
                    _ => None,
                };
                if let Some(body) = body {
                    assert!(
                        binding.callable_got_slot().is_none(),
                        "generic uniform body {}/{name} must remain slot-less",
                        module.key()
                    );
                    roster.insert(format!("{}/{name}: {body}", module.key()));
                }
            }
        }
        let expected = std::collections::BTreeSet::from([
            "primitives/bind: HostPromised".to_string(),
            "primitives/catch-runtime-error: HostPromised".to_string(),
            "primitives/race: HostPromised".to_string(),
            "primitives/select: HostPromised".to_string(),
        ]);
        assert_eq!(
            roster, expected,
            "an added or reclassified generic uniform body introduces a new backend representation dependency"
        );
    }

    #[test]
    fn next_type_id_advances_monotonically() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id).expect("bootstrap mount");
        // SList(1) + Option(1) + Pair(2) + Result(2) + IO(1) + Bind(2)
        // + bind(2) + race(1) + select(1) + catch-runtime-error(1) = 14 fresh vars.
        // (S96 Chunk C: `register_combinators` mints one var each for race + select.)
        assert_eq!(next_id.load(Ordering::SeqCst), 14);
    }
}
