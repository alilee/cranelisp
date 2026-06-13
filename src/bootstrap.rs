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
//!    `catch-runtime-error` (`DefKind::Primitive`, body in
//!    `cranelisp-intrinsics::panic`). `TestResult`/`run-test` RETIRED
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

use cranelisp_types::{
    DefKind, DefnVariant, Expr, FQSymbol, FQTypeName, ModuleEntry, ModuleFullPath, Scheme, Span,
    Symbol, Type, TypeDefInfo, TypeExpr, TypeId, Visibility,
};
use cranelisp_types::TypeName;

use crate::code::SessionSymbolTable;

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
/// `register_type_def_with_ctor_infos` cascade does (S79 Option 3a, FIXME 0319):
///
/// - **Sum/enum** (distinct ctor names — `Option`/`Result`/`IO`): a separate
///   `ModuleEntry::TypeDef` entry keyed by the type name carrying the
///   constructor-name list, plus one got-slotted `ModuleEntry::Def { kind:
///   DefKind::Constructor { type_def: None, .. } }` per constructor.
/// - **Single-ctor product** (type-name == sole ctor-name — `Pair`): NO separate
///   `TypeDef` entry. The lone ctor's got-slotted `Def` IS the `"Pair"` key and
///   carries the **type facet** `DefKind::Constructor { type_def: Some(..) }`, so
///   the same entry answers both as a constructor AND as its own type. The
///   retired `ModuleEntry::TypeDef.constructor_scheme` smuggling field is gone —
///   the product ctor's scheme lives on its own `Def.scheme`, its field names on
///   `Def.param_names`.
///
/// Each ctor `Def` has a scheme `forall [type_vars]. (Fn [field-tys] ADT)` (or
/// bare `ADT` for nullary), `param_names` = field names, and an `ast` carrying a
/// synthesised `DefnVariant` whose body is `Expr::ConstrADT`.
///
/// `type_var_ids` are the (already-allocated) ids quantified in each ctor
/// scheme; `adt_type` is `Type::ADT(fqtn, [Var(id)…])`.
fn register_synth_adt(
    module: &mut SessionSymbolTable,
    fqtn: &FQTypeName,
    type_name: &str,
    type_params: &[&str],
    type_var_ids: &[TypeId],
    adt_docstring: Option<&str>,
    ctors: &[SynthCtor],
) {
    let adt_type = Type::ADT(
        fqtn.clone(),
        type_var_ids.iter().map(|&id| Type::Var(id)).collect(),
    );

    // **Product/sum split (S79 Option 3a, FIXME 0319), mirroring
    // `register_type_def_with_ctor_infos`.** A single-ctor **product** (type
    // name == sole ctor name, e.g. `Pair`) has its type and constructor collide
    // on one symbol-table key. Rather than overwrite the got-slotted ctor `Def`
    // with a `TypeDef` (the old model — which dropped `param_names` field names),
    // the surviving `"Pair"` entry is the got-slotted ctor `Def` carrying a
    // **type facet** (`type_def: Some(..)`). A sum/enum type registers a separate
    // `TypeDef` and its ctors carry `type_def: None`.
    let constructors: Vec<Symbol> = ctors.iter().map(|c| Symbol::from(c.name)).collect();
    let type_def_info = TypeDefInfo {
        name: fqtn.clone(),
        type_params: type_params.iter().map(|p| Symbol::from(*p)).collect(),
        constructors,
    };
    let is_product = ctors.len() == 1 && ctors[0].name == type_name;

    for (tag, ctor) in ctors.iter().enumerate() {
        let param_names: Vec<Symbol> =
            ctor.fields.iter().map(|f| Symbol::from(f.name)).collect();

        // Scheme: nullary → ADT; data ctor → (Fn [field-tys] ADT).
        let scheme = if ctor.fields.is_empty() {
            Scheme {
                type_vars: type_var_ids.to_vec(),
                constraints: HashMap::new(),
                ty: adt_type.clone(),
            }
        } else {
            Scheme {
                type_vars: type_var_ids.to_vec(),
                constraints: HashMap::new(),
                ty: Type::Fn(
                    ctor.fields.iter().map(|f| f.ty.clone()).collect(),
                    Box::new(adt_type.clone()),
                ),
            }
        };

        // The product ctor (type-name == ctor-name) carries the type facet;
        // sum/enum ctors carry `type_def: None`.
        let ctor_type_def: Option<Box<TypeDefInfo>> = if is_product {
            Some(Box::new(type_def_info.clone()))
        } else {
            None
        };

        // Synthesise the DefnVariant body wrapping Expr::ConstrADT — backend
        // lowers this directly (DefKind::Constructor metadata is for pattern
        // matching + introspection, not codegen).
        let body_span = Span::SYNTHETIC;
        let synth_params: Vec<(Symbol, Option<TypeExpr>)> =
            param_names.iter().cloned().map(|n| (n, None)).collect();
        let synth_body = Expr::ConstrADT {
            type_name: fqtn.clone(),
            tag,
            fields: param_names
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
        let ast = DefnVariant {
            params: synth_params,
            body: synth_body,
            span: body_span,
        };

        let mut builder = ModuleEntry::def(
            scheme,
            DefKind::Constructor {
                type_name: fqtn.clone(),
                tag,
                field_count: ctor.fields.len(),
                internal: ctor.internal,
                type_def: ctor_type_def,
            },
        )
        .visibility(Visibility::Public)
        .param_names(param_names)
        .ast(ast);
        // The product ctor has no separate TypeDef to hold the deftype-level
        // docstring, so fall back to it when the ctor itself has none.
        let ctor_doc = ctor.docstring.or(if is_product { adt_docstring } else { None });
        if let Some(doc) = ctor_doc {
            builder = builder.docstring(doc);
        }
        module.insert(Symbol::from(ctor.name), builder.build());
    }

    // Register the sum/enum type's separate `TypeDef` entry (carries the
    // constructor-name list). The product case has NO `TypeDef` — its type facet
    // lives on the ctor `Def` registered above, under the shared type-name key.
    if !is_product {
        let docstring = adt_docstring.map(|d| d.to_string());
        module.insert(
            Symbol::from(type_name),
            ModuleEntry::TypeDef {
                info: type_def_info,
                visibility: Visibility::Public,
                docstring,
            },
        );
    }
}

/// Insert a `DefKind::Primitive` `Def` entry into `module`.
fn insert_primitive(
    module: &mut SessionSymbolTable,
    name: &str,
    scheme: Scheme,
    param_names: Vec<&str>,
    docstring: &str,
) {
    module.insert(
        Symbol::from(name),
        ModuleEntry::def(scheme, DefKind::Primitive)
            .visibility(Visibility::Public)
            .param_names(param_names.into_iter().map(Symbol::from).collect())
            .docstring(docstring)
            .build(),
    );
}

/// Mount the synthetic modules into `symbol_tables`. Replaces the deleted
/// `cranelisp_typecheck::register_builtins` (FIXME 0242). The caller has
/// already mounted `user` and `primitives` (via `PRIMITIVES_TABLE`) before
/// this runs.
pub(crate) fn mount_synthetic_modules(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) {
    ensure_module(symbol_tables, &ModuleFullPath::from("primitives"));
    ensure_module(symbol_tables, &ModuleFullPath::from(""));

    register_special_forms(symbol_tables); // step 1
    register_builtin_type_names(symbol_tables); // step 2
    register_macros_module(symbol_tables, next_id); // step 3
    register_option_type(symbol_tables, next_id); // step 4
    register_pair_type(symbol_tables, next_id); // step 4b (test-discovery.md ruling 1)
    register_result_type(symbol_tables, next_id); // step 4c (test-discovery.md ruling 1)
    register_io_type(symbol_tables, next_id); // step 5
    register_bind_primitive(symbol_tables, next_id); // step 6
    register_trace_type(symbol_tables); // step 7
    register_test_infrastructure(symbol_tables, next_id); // step 8
}

/// Ensure a module exists in the session table.
fn ensure_module(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    path: &ModuleFullPath,
) {
    if !symbol_tables.contains_key(path) {
        symbol_tables.insert(path.clone(), SessionSymbolTable::new_with_params(path.clone()));
    }
}

// --- Step 1: special forms (root "") ---

fn register_special_forms(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
) {
    let special_forms = [
        ("if", "conditional: (if cond then else)"),
        ("let", "local binding: (let [x e] body)"),
        ("fn", "lambda: (fn [params] body)"),
        ("defn", "function definition: (defn name [params] body)"),
        ("deftype", "type definition: (deftype Name ctor1 ctor2 ...)"),
        ("match", "pattern matching: (match expr [pat body] ...)"),
        (
            "deftrait",
            "trait declaration: (deftrait (TraitName a) (method [a ...] ret) ...)",
        ),
        (
            "impl",
            "trait implementation: (impl TraitName Type (method [params] body) ...)",
        ),
        ("defmacro", "macro definition: (defmacro name [params] body)"),
    ];

    let root_path = ModuleFullPath::from("");
    let mut root = symbol_tables
        .get_mut(&root_path)
        .unwrap_or_else(|| unreachable!("invariant: root \"\" module should exist (bootstrap)"));
    for (name, desc) in special_forms {
        root.insert(
            Symbol::from(name),
            ModuleEntry::SpecialForm {
                scheme: mono(Type::Int),
                param_names: vec![],
                docstring: Some(desc.to_string()),
                description: desc.to_string(),
                visibility: Visibility::Public,
            },
        );
    }

    // `trace` is a ROOT special form (user ruling 2026-06-04; tracing.md §3.1,
    // spec §4.12.4): `(trace expr)` is recognised parser-side as `Expr::Trace`
    // and needs NO import — exactly like `if`/`let`. Its SpecialForm metadata
    // (self-documenting-REPL feedback for `/info trace`) therefore lives at root
    // `""`, alongside the other root special forms — NOT in `primitives`. The
    // `Trace`/`TraceCall` ADT names + their accessors STAY in `primitives`
    // (form/ADT asymmetry, spec §3.2.4); only the *form* name `trace` is here.
    // The richer scheme/param metadata is preserved (the structural forms above
    // carry only a placeholder scheme; `trace` carries its real shape).
    let trace_ty = Type::ADT(primitives_fqtn("Trace"), vec![]);
    let trace_form_desc = "Execution trace: (trace expr) — evaluates expr with call instrumentation, returns Trace ADT";
    root.insert(
        Symbol::from("trace"),
        ModuleEntry::SpecialForm {
            scheme: mono(Type::Fn(
                vec![Type::Var(0)], // any expression type
                Box::new(trace_ty),
            )),
            param_names: vec![Symbol::from("expr")],
            docstring: Some(trace_form_desc.to_string()),
            description: trace_form_desc.to_string(),
            visibility: Visibility::Public,
        },
    );
}

// --- Step 2: intrinsic type names (primitives) ---

fn register_builtin_type_names(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
) {
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
    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

    for (name, ty, desc) in intrinsic_scalars {
        primitives.insert(
            Symbol::from(name),
            ModuleEntry::IntrinsicType {
                ty,
                visibility: Visibility::Public,
                docstring: Some(desc.to_string()),
            },
        );
    }

    // Vec stays as TypeDef — no Type::Vec variant (vec is Type::ADT(Vec, [elem])).
    // It has no surface constructor, so it is not a product (no type facet).
    primitives.insert(
        Symbol::from("Vec"),
        ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: primitives_fqtn("Vec"),
                type_params: vec![],
                constructors: vec![],
            },
            visibility: Visibility::Public,
            docstring: Some("builtin vector type".to_string()),
        },
    );
}

// --- Step 3: synthetic `macros` module (SList, Sexp, sconcat) ---

fn register_macros_module(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) {
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
        let mut macros = symbol_tables
            .get_mut(&macros_path)
            .unwrap_or_else(|| unreachable!("invariant: macros module should exist"));
        for sym in ["Int", "Bool", "Float", "String"] {
            macros.insert(
                Symbol::from(sym),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: primitives_path.clone(),
                        symbol: Symbol::from(sym),
                    },
                    visibility: Visibility::Private,
                },
            );
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
            .unwrap_or_else(|| unreachable!("invariant: macros module should exist"));
        register_synth_adt(
            &mut macros,
            &slist_fqtn,
            "SList",
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
        );
    }

    // Sexp: 7 single-field data constructors.
    let sexp_fqtn = macros_fqtn("Sexp");
    let sexp_ty = Type::ADT(sexp_fqtn.clone(), vec![]);
    let slist_sexp = Type::ADT(slist_fqtn.clone(), vec![sexp_ty.clone()]);
    {
        let mut macros = symbol_tables
            .get_mut(&macros_path)
            .unwrap_or_else(|| unreachable!("invariant: macros module should exist"));
        register_synth_adt(
            &mut macros,
            &sexp_fqtn,
            "Sexp",
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
            ],
        );

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
        );
    }
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
) {
    let primitives_path = ModuleFullPath::from("primitives");
    let option_a = fresh_type_id(next_id);
    let option_fqtn = primitives_fqtn("Option");
    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));
    register_synth_adt(
        &mut primitives,
        &option_fqtn,
        "Option",
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
    );
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
) {
    let primitives_path = ModuleFullPath::from("primitives");
    let pair_a = fresh_type_id(next_id);
    let pair_b = fresh_type_id(next_id);
    let pair_fqtn = primitives_fqtn("Pair");
    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));
    register_synth_adt(
        &mut primitives,
        &pair_fqtn,
        "Pair",
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
    );
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
) {
    let primitives_path = ModuleFullPath::from("primitives");
    let result_a = fresh_type_id(next_id);
    let result_b = fresh_type_id(next_id);
    let result_fqtn = primitives_fqtn("Result");
    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));
    register_synth_adt(
        &mut primitives,
        &result_fqtn,
        "Result",
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
    );
}

// --- Step 5: IO ADT (primitives) ---

fn register_io_type(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) {
    let primitives_path = ModuleFullPath::from("primitives");
    let io_a = fresh_type_id(next_id);
    let io_fqtn = primitives_fqtn("IO");

    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

    // Pure / Effect via the standard ADT path.
    register_synth_adt(
        &mut primitives,
        &io_fqtn,
        "IO",
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
    );

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
    if let Some(ModuleEntry::TypeDef { info, .. }) = primitives.symbols.get_mut(&Symbol::from("IO"))
    {
        info.constructors.push(Symbol::from("Bind"));
    } else {
        unreachable!("invariant: IO type should be registered before adding Bind");
    }
    primitives.insert(
        Symbol::from("Bind"),
        ModuleEntry::def(
            bind_ctor_scheme,
            DefKind::Constructor {
                type_name: io_fqtn.clone(),
                tag: 2,
                field_count: 2,
                internal: true,
                // `IO` is a sum type (`Pure`/`Effect`/`Bind`) with a separate
                // `TypeDef`; `Bind` is not its own type.
                type_def: None,
            },
        )
        .visibility(Visibility::Public)
        .docstring("Chain IO actions (internal — constructed by bind primitive)")
        .param_names(bind_param_names)
        .ast(DefnVariant {
            params: synth_params,
            body: synth_body,
            span: body_span,
        })
        .build(),
    );
}

// --- Step 6: bind primitive (primitives) ---

fn register_bind_primitive(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) {
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
        .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));
    primitives.insert(
        Symbol::from("bind"),
        ModuleEntry::def(bind_scheme, DefKind::Primitive)
            .visibility(Visibility::Public)
            .docstring(
                "Chain IO actions: extract value from first IO, pass to continuation",
            )
            .param_names(vec![Symbol::from("io"), Symbol::from("f")])
            .build(),
    );
}

// --- Step 7: Trace ADT + field accessors + `trace` form (primitives) ---

fn register_trace_type(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
) {
    let primitives_path = ModuleFullPath::from("primitives");
    let trace_fqtn = primitives_fqtn("Trace");
    let trace_ty = Type::ADT(trace_fqtn.clone(), vec![]);
    let slist_string = Type::ADT(macros_fqtn("SList"), vec![Type::String]);
    let slist_trace = Type::ADT(macros_fqtn("SList"), vec![trace_ty.clone()]);

    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

    register_synth_adt(
        &mut primitives,
        &trace_fqtn,
        "Trace",
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
    );

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
        insert_primitive(&mut primitives, field_name, scheme, vec!["t"], docstring);
    }

    // NOTE: the `trace` SpecialForm metadata entry is registered at ROOT `""`
    // (see `register_special_forms`, step 1), NOT here — `trace` is a root
    // special form needing no import (user ruling 2026-06-04; FIXME 0266
    // resolved). Only the `Trace`/`TraceCall` ADT + accessors live in
    // `primitives` (form/ADT asymmetry, spec §3.2.4).
}

// --- Step 8: test-discovery primitives (primitives) ---
//
// test-discovery.md (fourth convergence, SETTLED): `TestResult`/`run-test`
// RETIRE; `discover-tests` becomes a `DefKind::PrimitiveExtern` returning
// fn-value pairs; `catch-runtime-error` is a standalone `DefKind::Primitive`
// combinator backed by the `cranelisp-intrinsics::panic` C-ABI export.

fn register_test_infrastructure(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    next_id: &AtomicU32,
) {
    let primitives_path = ModuleFullPath::from("primitives");
    let mut primitives = symbol_tables
        .get_mut(&primitives_path)
        .unwrap_or_else(|| unreachable!("invariant: primitives module should exist"));

    // The eligible-test callable: `(Fn [] (Option String))` — None=pass,
    // (Some reason)=fail. The wrapper's own type and the eligibility filter
    // are the same contract (q-eligibility).
    let option_string = Type::ADT(primitives_fqtn("Option"), vec![Type::String]);
    let test_callable = Type::Fn(vec![], Box::new(option_string));
    // (Pair String (Fn [] (Option String)))
    let pair_name_callable = Type::ADT(
        primitives_fqtn("Pair"),
        vec![Type::String, test_callable],
    );
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
    primitives.insert(
        Symbol::from("discover-tests"),
        ModuleEntry::def(
            mono(Type::Fn(vec![vec_string], Box::new(vec_pairs))),
            DefKind::PrimitiveExtern,
        )
        .visibility(Visibility::Public)
        .param_names(vec![Symbol::from("modules")])
        .docstring(
            "Discover eligible test-* functions across the given module paths: \
             returns (Vec (Pair name late-bound-callable)).",
        )
        .build(),
    );

    // catch-runtime-error :: forall a. (Fn [(Fn [] a)] (Result a String))
    //
    // A plain forall scheme with EMPTY constraints (modelled on
    // `register_bind_primitive`) — one runtime body serves every `a` (uniform
    // i64 ABI), so the constrained-fn monomorphisation machinery is NOT
    // engaged. JIT name = ABI name = "catch-runtime-error" — resolved from the
    // intrinsics archive (intrinsics_table() entry); no `define_symbol`.
    let a = fresh_type_id(next_id);
    let thunk_ty = Type::Fn(vec![], Box::new(Type::Var(a)));
    let result_a_string = Type::ADT(
        primitives_fqtn("Result"),
        vec![Type::Var(a), Type::String],
    );
    let cre_scheme = Scheme {
        type_vars: vec![a],
        constraints: HashMap::new(),
        ty: Type::Fn(vec![thunk_ty], Box::new(result_a_string)),
    };
    primitives.insert(
        Symbol::from("catch-runtime-error"),
        ModuleEntry::def(cre_scheme, DefKind::Primitive)
            .visibility(Visibility::Public)
            .param_names(vec![Symbol::from("thunk")])
            .docstring(
                "Invoke a thunk under runtime-error protection: returns \
                 (Ok result) on success or (Err message) on a runtime panic.",
            )
            .build(),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn mounts_special_forms_at_root() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id);
        let root = tables.get(&ModuleFullPath::from("")).unwrap();
        assert!(matches!(
            root.get("if"),
            Some(ModuleEntry::SpecialForm { .. })
        ));
        assert!(matches!(
            root.get("defmacro"),
            Some(ModuleEntry::SpecialForm { .. })
        ));
    }

    #[test]
    fn mounts_intrinsic_scalars_in_primitives() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id);
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        assert!(matches!(
            prims.get("Int"),
            Some(ModuleEntry::IntrinsicType { ty: Type::Int, .. })
        ));
        assert!(matches!(
            prims.get("Vec"),
            Some(ModuleEntry::TypeDef { .. })
        ));
    }

    #[test]
    fn mounts_macros_sexp_and_slist() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id);
        let macros = tables.get(&ModuleFullPath::from("macros")).unwrap();
        assert!(matches!(macros.get("Sexp"), Some(ModuleEntry::TypeDef { .. })));
        assert!(matches!(macros.get("SList"), Some(ModuleEntry::TypeDef { .. })));
        // SCons is a data constructor Def.
        assert!(matches!(
            macros.get("SCons"),
            Some(ModuleEntry::Def {
                kind,
                ..
            }) if matches!(kind.as_ref(), DefKind::Constructor { .. })
        ));
        assert!(matches!(macros.get("sconcat"), Some(ModuleEntry::Def { .. })));
    }

    #[test]
    fn mounts_option_io_bind() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id);
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        assert!(matches!(prims.get("Option"), Some(ModuleEntry::TypeDef { .. })));
        assert!(matches!(prims.get("Some"), Some(ModuleEntry::Def { .. })));
        assert!(matches!(prims.get("IO"), Some(ModuleEntry::TypeDef { .. })));
        assert!(matches!(prims.get("bind"), Some(ModuleEntry::Def { .. })));
        // Bind is internal.
        match prims.get("Bind") {
            Some(ModuleEntry::Def { kind, .. }) => match kind.as_ref() {
                DefKind::Constructor { internal, tag, .. } => {
                    assert!(*internal);
                    assert_eq!(*tag, 2);
                }
                _ => panic!("Bind should be DefKind::Constructor"),
            },
            _ => panic!("Bind should be a Def"),
        }
        // IO has 3 constructors recorded.
        if let Some(ModuleEntry::TypeDef { info, .. }) = prims.get("IO") {
            assert_eq!(info.constructors.len(), 3);
        }
    }

    #[test]
    fn mounts_trace_and_test_infrastructure() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id);
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        assert!(matches!(prims.get("Trace"), Some(ModuleEntry::TypeDef { .. })));
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
            matches!(root.get("trace"), Some(ModuleEntry::SpecialForm { .. })),
            "trace SpecialForm metadata must resolve at root \"\""
        );
        // TestResult / run-test RETIRED (test-discovery.md, fourth convergence).
        assert!(prims.get("TestResult").is_none(), "TestResult must be retired");
        assert!(prims.get("run-test").is_none(), "run-test must be retired");
        // discover-tests is now a PrimitiveExtern (host-promised body).
        assert!(matches!(
            prims.get("discover-tests"),
            Some(ModuleEntry::Def { kind, got_slot: None, .. })
                if matches!(kind.as_ref(), DefKind::PrimitiveExtern)
        ));
    }

    #[test]
    fn mounts_pair_and_result_in_primitives() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id);
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
            Some(ModuleEntry::Def { kind, scheme, param_names, .. }) => {
                match kind.as_ref() {
                    DefKind::Constructor { type_def: Some(td), field_count, .. } => {
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
                    param_names,
                    &vec![Symbol::from("first"), Symbol::from("second")],
                    "Pair field names ride on the ctor Def's param_names"
                );
                match &scheme.ty {
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
        assert!(matches!(prims.get("Result"), Some(ModuleEntry::TypeDef { .. })));
        // Ok=tag 0, Err=tag 1 (declaration order — the combinator assumes this).
        match prims.get("Ok") {
            Some(ModuleEntry::Def { kind, .. }) => match kind.as_ref() {
                DefKind::Constructor { tag, field_count, .. } => {
                    assert_eq!(*tag, 0);
                    assert_eq!(*field_count, 1);
                }
                _ => panic!("Ok should be a Constructor"),
            },
            other => panic!("Ok should be a Def, got {other:?}"),
        }
        match prims.get("Err") {
            Some(ModuleEntry::Def { kind, .. }) => match kind.as_ref() {
                DefKind::Constructor { tag, .. } => assert_eq!(*tag, 1),
                _ => panic!("Err should be a Constructor"),
            },
            other => panic!("Err should be a Def, got {other:?}"),
        }
    }

    #[test]
    fn mounts_catch_runtime_error_primitive() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id);
        let prims = tables.get(&ModuleFullPath::from("primitives")).unwrap();
        match prims.get("catch-runtime-error") {
            Some(ModuleEntry::Def { kind, scheme, .. }) => {
                assert!(matches!(kind.as_ref(), DefKind::Primitive));
                // forall a. (Fn [(Fn [] a)] (Result a String)) — one quantified
                // var, empty constraints (plain forall, not constrained-fn).
                assert_eq!(scheme.type_vars.len(), 1);
                assert!(scheme.constraints.is_empty());
            }
            other => panic!("catch-runtime-error should be a Primitive Def, got {other:?}"),
        }
    }

    #[test]
    fn next_type_id_advances_monotonically() {
        let (tables, next_id) = fresh_tables();
        mount_synthetic_modules(&tables, &next_id);
        // SList(1) + Option(1) + Pair(2) + Result(2) + IO(1) + Bind(2)
        // + bind(2) + catch-runtime-error(1) = 12 fresh vars.
        assert_eq!(next_id.load(Ordering::SeqCst), 12);
    }
}
