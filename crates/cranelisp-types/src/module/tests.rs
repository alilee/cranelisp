use super::*;
use crate::{
    DefnVariant, Expr, FQSymbol, FQTraitName, FQTypeName, ModuleFullPath, ModuleName, Scheme, Span,
    Symbol, TraitName, Type, TypeDefInfo, TypeName, Visibility,
};
use std::collections::HashMap;

// ---- Sprint 56 Wave 0 §9.5 — defined_symbols filter predicate ----

/// Build a minimal `ModuleEntry::Def` for test fixtures.
fn mk_def(kind: DefKind, ast: Option<DefnVariant>) -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(kind),
        callees: Vec::new(),
        value_use: false,
        trait_origin: None,
        seq: 0,
        ast,
        codegen_view: None,
        code: None,
    }
}

/// A trivial `DefnVariant` used as an `ast` payload for tests (S69 Submission 35
/// narrowed `ModuleEntry::Def.ast` from `Option<Defn>` to `Option<DefnVariant>`).
/// The `_name` parameter is retained at call sites for readability but no longer
/// threads into the payload (the entry's own symbol-table key carries the name).
fn trivial_variant(_name: &str) -> DefnVariant {
    DefnVariant {
        params: vec![],
        body: Expr::IntLit {
            value: 0,
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        },
        span: Span::SYNTHETIC,
    }
}

// `trivial_defn` test helper retired in S70 Phase 3 alongside
// `ConstrainedFn { defn: Defn }` → `{ variant: DefnVariant }` narrow.
// Tests construct `ConstrainedFn { variant: trivial_variant(name), .. }`
// directly — the outer `Defn` wrapper duplicated metadata already on the
// parent `Def` entry (parallel to S69 Submission 35's `Def.ast` narrow).

// spec: design/typecheck/ast-annotation.md §9.5 — defined_symbols filter predicate
#[test]
fn wave0_defined_symbols_filter_is_correct() {
    let mut st = SymbolTable::new(ModuleFullPath::from("user"));

    // (a) Regular UserFn with ast: Some(_) — SHOULD appear.
    st.insert(
        Symbol::from("regular"),
        mk_def(
            DefKind::UserFn {
                fn_state: UserFnState::NotDetermined,
            },
            Some(trivial_variant("regular")),
        ),
    );

    // (b) Overloaded base with ast: None — MUST NOT appear.
    st.insert(
        Symbol::from("overloaded_base"),
        mk_def(DefKind::Overloaded { variants: vec![] }, None),
    );

    // (c) UserFn template with constrained_fn: Some(_) — MUST NOT appear,
    // even if ast happens to be Some(_) (§9.5 filter excludes templates by kind).
    let template_cf = ConstrainedFn {
        variant: trivial_variant("template"),
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
    };
    st.insert(
        Symbol::from("template"),
        mk_def(
            DefKind::UserFn {
                fn_state: UserFnState::Constrained(Box::new(template_cf)),
            },
            Some(trivial_variant("template")),
        ),
    );

    // (d) TypeDef — not a Def variant at all; MUST NOT appear.
    st.insert(
        Symbol::from("MyType"),
        ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("MyType")),
                type_params: vec![],
                constructors: vec![],
            },
            visibility: Visibility::Public,
            docstring: None,
        },
    );

    // (e) Import — not a Def variant; MUST NOT appear.
    st.insert(
        Symbol::from("imported"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("some-prim"),
            },
            visibility: Visibility::Private,
        },
    );

    // (f) Mangled multi-sig variant with ast: Some(_) — SHOULD appear.
    st.insert(
        Symbol::from("add$Int+Int"),
        mk_def(
            DefKind::UserFn {
                fn_state: UserFnState::NotDetermined,
            },
            Some(trivial_variant("add$Int+Int")),
        ),
    );

    let names: std::collections::HashSet<String> = st
        .defined_symbols()
        .map(|(s, _)| s.as_ref().to_string())
        .collect();

    assert!(
        names.contains("regular"),
        "regular UserFn with ast: Some(..) must appear; got {:?}",
        names
    );
    assert!(
        names.contains("add$Int+Int"),
        "mangled multi-sig variant with ast: Some(..) must appear; got {:?}",
        names
    );
    assert!(
        !names.contains("overloaded_base"),
        "Overloaded base must NOT appear; got {:?}",
        names
    );
    assert!(
        !names.contains("template"),
        "constrained-fn template must NOT appear; got {:?}",
        names
    );
    assert!(
        !names.contains("MyType"),
        "TypeDef must NOT appear; got {:?}",
        names
    );
    assert!(
        !names.contains("imported"),
        "Import must NOT appear; got {:?}",
        names
    );
}

// spec: design/arch/concrete-boundary-type.md §4 Phase 4(B) —
//       a slot-less `UserFnState::Polymorphic` generic template is a mono
//       SOURCE, never a codegen target (FIXME 0381). It MUST NOT appear in
//       `defined_symbols()` (symmetric with `Constrained`); only its
//       concrete monomorphised instances codegen.
#[test]
fn polymorphic_template_excluded_from_defined_symbols() {
    let mut st = SymbolTable::new(ModuleFullPath::from("user"));

    // The slot-less Polymorphic generic template (e.g. `(defn id [x] x)`).
    let parametric = ParametricFn {
        variant: trivial_variant("id"),
        scheme: Scheme {
            type_vars: vec![0],
            constraints: HashMap::new(),
            ty: Type::Var(0),
        },
    };
    st.insert(
        Symbol::from("id"),
        mk_def(
            DefKind::UserFn {
                fn_state: UserFnState::Polymorphic(Box::new(parametric)),
            },
            // Even though the template body is present (ast: Some), it MUST
            // NOT be a codegen target.
            Some(trivial_variant("id")),
        ),
    );

    // Its concrete monomorphised instance (`id$Int`) — a `Concrete` UserFn
    // — IS a codegen target and SHOULD appear.
    st.insert(
        Symbol::from("id$Int"),
        mk_def(
            DefKind::UserFn {
                fn_state: UserFnState::Concrete {
                    got_slot: 0,
                    mode_summary: None,
                },
            },
            Some(trivial_variant("id$Int")),
        ),
    );

    let names: std::collections::HashSet<String> = st
        .defined_symbols()
        .map(|(s, _)| s.as_ref().to_string())
        .collect();

    assert!(
        !names.contains("id"),
        "Polymorphic generic template must NOT be a codegen target; got {:?}",
        names
    );
    assert!(
        names.contains("id$Int"),
        "concrete mono instance id$Int must appear; got {:?}",
        names
    );
}

// spec: design/arch/bounded-contexts.md §7 "Callability is structural" +
//       design/arch/principles/20-model-invariants-by-representation.md —
//       the slot lives on the callable DefKind variants, so a constrained
//       template structurally CANNOT hold a callable slot (the 0356/0357
//       representation fix; superseded the S82 0354 accessor stopgap).
//       Structural guard (per /qa's S83 re-point): callable_got_slot() is
//       Some for a Concrete UserFn / Primitive / Constructor and None for a
//       Constrained template, a NotDetermined interim fn, and the slot-less
//       kinds — and the illegal "constrained + slot" pairing is now
//       unconstructable (no field to set), proven by the type system, not
//       by an accessor reading around it.
#[test]
fn callable_got_slot_is_structural() {
    let cf = ConstrainedFn {
        variant: trivial_variant("cmp"),
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
    };

    // A concrete UserFn carries its slot on the kind's Concrete fn_state.
    let concrete: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Int),
        DefKind::UserFn {
            fn_state: UserFnState::Concrete {
                got_slot: 3,
                mode_summary: None,
            },
        },
    )
    .build();
    assert_eq!(concrete.callable_got_slot(), Some(3));
    assert!(!concrete.is_constrained_template());

    // A constrained template carries NO slot — there is no field to set.
    // (The once-illegal `Def{got_slot:Some} + constrained` shape from the
    // 0354 era is now unconstructable: Constrained has no got_slot.)
    let template: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Int),
        DefKind::UserFn {
            fn_state: UserFnState::Constrained(Box::new(cf)),
        },
    )
    .build();
    assert!(template.is_constrained_template());
    assert_eq!(
        template.callable_got_slot(),
        None,
        "a constrained template structurally has no callable slot"
    );

    // The Pass-1 interim NotDetermined fn is also slot-less → None.
    let interim: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Int),
        DefKind::UserFn {
            fn_state: UserFnState::NotDetermined,
        },
    )
    .build();
    assert_eq!(interim.callable_got_slot(), None);
    assert!(!interim.is_constrained_template());

    // Primitive and Constructor carry their (mandatory) slot too.
    let prim: ModuleEntry = ModuleEntry::def(mono_scheme(Type::Int), DefKind::primitive(9)).build();
    assert_eq!(prim.callable_got_slot(), Some(9));

    let ctor: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Int),
        DefKind::Constructor {
            got_slot: 11,
            type_name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Some")),
            tag: 0,
            field_count: 1,
            internal: false,
            type_def: None,
            mode_summary: None,
        },
    )
    .build();
    assert_eq!(ctor.callable_got_slot(), Some(11));
}

// ---- S109 Phase 3 — type_def_info: the single "answers as a type" reader ----

/// A `TypeDefInfo` fixture for `ty` in module `user`.
fn tdi(ty: &str, constructors: &[&str]) -> TypeDefInfo {
    TypeDefInfo {
        name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from(ty)),
        type_params: vec![],
        constructors: constructors.iter().map(|c| Symbol::from(*c)).collect(),
    }
}

// spec: spec/04-types.md §4.2 — both surviving type shapes answer as a type
// through ONE reader (S79 dual facet; FIXME 0573 root-cause class: a bare
// `ModuleEntry::TypeDef` match silently skips product types).
#[test]
fn type_def_info_answers_for_both_type_shapes() {
    // Sum/enum: a real `ModuleEntry::TypeDef` entry.
    let sum: ModuleEntry = ModuleEntry::TypeDef {
        info: tdi("Rotation", &["L", "R"]),
        visibility: Visibility::Public,
        docstring: None,
    };
    let info = sum
        .type_def_info()
        .expect("a TypeDef entry answers as a type");
    assert_eq!(info.name.name, TypeName::from("Rotation"));

    // Single-ctor product: the got-slotted ctor `Def` carrying the type facet
    // (type-name == ctor-name, S79 Option 3a).
    let product: ModuleEntry = mk_def(
        DefKind::Constructor {
            got_slot: 3,
            type_name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Position")),
            tag: 0,
            field_count: 1,
            internal: false,
            type_def: Some(Box::new(tdi("Position", &["Position"]))),
            mode_summary: None,
        },
        None,
    );
    let info = product
        .type_def_info()
        .expect("a product ctor Def with a type facet answers as a type");
    assert_eq!(info.name.name, TypeName::from("Position"));
    assert_eq!(info.constructors, vec![Symbol::from("Position")]);
}

// spec: spec/04-types.md §4.2 — entries that are NOT a type answer None:
// an ordinary sum ctor (type_def: None), a plain user fn, an import edge.
#[test]
fn type_def_info_none_for_non_type_entries() {
    let sum_ctor: ModuleEntry = mk_def(
        DefKind::Constructor {
            got_slot: 7,
            type_name: FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Rotation")),
            tag: 1,
            field_count: 1,
            internal: false,
            type_def: None,
            mode_summary: None,
        },
        None,
    );
    assert!(
        sum_ctor.type_def_info().is_none(),
        "an ordinary sum ctor is not its own type"
    );

    let user_fn: ModuleEntry = mk_def(
        DefKind::UserFn {
            fn_state: UserFnState::NotDetermined,
        },
        None,
    );
    assert!(
        user_fn.type_def_info().is_none(),
        "a plain Def never answers as a type"
    );

    let import: ModuleEntry = ModuleEntry::Import {
        source: FQSymbol {
            module: ModuleFullPath::from("lib"),
            symbol: Symbol::from("Position"),
        },
        visibility: Visibility::Private,
    };
    assert!(
        import.type_def_info().is_none(),
        "an import edge is not a type facet — chain-follow first, then read the terminal"
    );
}

// ---- Sprint 56 Wave 0 §9.8 — GotTable on SymbolTable ----

// spec: design/typecheck/ast-annotation.md §9.8 — GotTable on SymbolTable: presence + serde roundtrip
#[test]
fn wave0_symbol_table_got_present_and_serde_skipped() {
    // Build a SymbolTable and verify `got` is live and addressable.
    let mut st = SymbolTable::new(ModuleFullPath::from("user"));

    // base_ptr() is non-null and stable across reads.
    let p1 = st.got.base_ptr();
    let p2 = st.got.base_ptr();
    assert!(
        !p1.is_null(),
        "fresh SymbolTable's GOT base pointer must be non-null"
    );
    assert_eq!(p1, p2, "GOT base_ptr() must be stable across reads");

    // Slot bookkeeping before and after allocation.
    assert_eq!(st.next_got_slot, 0);
    let s0 = st.allocate_got_slot().expect("fresh table has free slots");
    let s1 = st.allocate_got_slot().expect("fresh table has free slots");
    assert_eq!(s0, 0);
    assert_eq!(s1, 1);
    assert_eq!(st.next_got_slot, 2);

    // Allocation does not move the GOT array in memory.
    assert_eq!(st.got.base_ptr(), p1);

    // Insert one entry to prove serde roundtrip preserves symbol data.
    st.insert(
        Symbol::from("entry"),
        mk_def(
            DefKind::UserFn {
                fn_state: UserFnState::NotDetermined,
            },
            Some(trivial_variant("entry")),
        ),
    );

    // Write a known pointer through the GOT and read it back (round-trip
    // of the runtime pointer must NOT survive serde — verified below).
    let fake_ptr = 0xDEAD_BEEFusize as *const u8;
    st.got.store_slot(s0, fake_ptr);
    assert_eq!(st.got.load_slot(s0), fake_ptr);

    // Serialize and deserialize. The `got` field is `#[serde(skip)]` so it
    // must NOT round-trip the runtime pointer; a fresh null GOT is expected.
    let json = serde_json::to_string(&st).expect("SymbolTable must serialize");
    assert!(
        !json.contains("DEADBEEF") && !json.contains("deadbeef"),
        "serialized form must not contain runtime pointer values: {}",
        json
    );
    let rt: SymbolTable = serde_json::from_str(&json).expect("SymbolTable must deserialize");

    // next_got_slot bookkeeping is preserved across the roundtrip.
    assert_eq!(
        rt.next_got_slot, 2,
        "next_got_slot must round-trip via serde"
    );

    // The deserialized GOT exists (#[serde(default)] reconstructs it), has a
    // valid base pointer, and all slots start null (runtime state NOT
    // round-tripped — §9.8.3 Serde semantics).
    let rt_base = rt.got.base_ptr();
    assert!(
        !rt_base.is_null(),
        "deserialized SymbolTable must have a live GOT (non-null base_ptr)"
    );
    assert!(
        rt.got.load_slot(s0).is_null(),
        "deserialized GOT must reset slot pointers to null"
    );
    assert!(
        rt.got.load_slot(s1).is_null(),
        "deserialized GOT must reset every slot to null"
    );

    // Symbol payload (non-runtime) survives the roundtrip.
    assert!(rt.get("entry").is_some(), "entry must round-trip");
}

// ---- Sprint 57 Wave 2 Step 1 — Decision 25: `code` field on ModuleEntry::Def ----

// spec: design/arch/CLAUDE.md Decision 25 / design/typecheck/ast-annotation.md §10.1 —
//       `code: Option<Code>` present and defaults to None on fresh construction.
#[test]
fn module_entry_def_has_code_field_none_by_default() {
    let entry = mk_def(
        DefKind::UserFn {
            fn_state: UserFnState::NotDetermined,
        },
        Some(trivial_variant("fresh")),
    );
    match entry {
        ModuleEntry::Def { code, .. } => {
            assert!(
                code.is_none(),
                "freshly constructed ModuleEntry::Def must have code: None; got {:?}",
                code
            );
        }
        other => panic!("expected ModuleEntry::Def, got {:?}", other),
    }
}

// spec: design/arch/CLAUDE.md Decision 25 + Sprint 58 Wave 3b (Decision 35) —
//       #[serde(skip)] on the `code: Option<C>` field; runtime-only, never
//       round-trips through the cache manifest. Wave 3b note: the old
//       `cranelisp_types::Code` pointer-only struct is gone; the field is
//       now generic over `C: CodeStore`. This test exercises the `()`
//       default flavour (typecheck-side view); the integration-layer
//       enum-flavour serde is exercised in `src/code.rs::tests`.
#[test]
fn code_serialise_round_trip_skips_field() {
    let entry: ModuleEntry<()> = ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::UserFn {
            fn_state: UserFnState::NotDetermined,
        }),
        callees: Vec::new(),
        value_use: false,
        trait_origin: None,
        seq: 0,
        ast: Some(trivial_variant("with_code")),
        codegen_view: None,
        // `()` flavour — Some/None of the unit type. Serde discipline
        // is the same regardless of `C`.
        code: Some(()),
    };

    let json = serde_json::to_string(&entry).expect("entry must serialize");
    // Field must not appear in the serialised form.
    assert!(
        !json.contains("\"code\""),
        "serialised form must not contain the `code` field (it is #[serde(skip)]): {}",
        json
    );

    let rt: ModuleEntry = serde_json::from_str(&json).expect("entry must deserialize");
    match rt {
        ModuleEntry::Def { code, ast, .. } => {
            assert!(
                code.is_none(),
                "deserialised ModuleEntry::Def must have code: None (serde(skip)); got {:?}",
                code
            );
            assert!(
                ast.is_some(),
                "ast must survive the roundtrip so codegen can repopulate code from it"
            );
        }
        other => panic!("expected ModuleEntry::Def, got {:?}", other),
    }
}

// ---- Sprint 66 Wave 0 amendment — fn_ptr removed; GOT is the single source of truth ----

// spec: design/arch/bounded-contexts.md §7 "Callability is structural" +
//       Principle 20 — the GOT slot lives on the callable DefKind variants,
//       not as a flat field. A freshly registered user fn is the Pass-1
//       interim `UserFnState::NotDetermined`, which is slot-less by
//       construction, so `callable_got_slot()` is None. The slot is
//       allocated only at the determination point (constructing
//       `UserFnState::Concrete`), per the deferred-allocation timing-wall
//       resolution (gating decision 3).
#[test]
fn fresh_module_entry_def_has_no_callable_slot() {
    let entry = mk_def(
        DefKind::UserFn {
            fn_state: UserFnState::NotDetermined,
        },
        Some(trivial_variant("fresh")),
    );
    assert!(
        matches!(entry, ModuleEntry::Def { .. }),
        "expected ModuleEntry::Def"
    );
    assert_eq!(
        entry.callable_got_slot(),
        None,
        "a freshly registered (NotDetermined) user fn has no callable slot"
    );
}

// spec: design/arch/CLAUDE.md Decision 26 (Option B — variant-internal) —
//       DefKind::PlatformEffect { scheduling_class } carries the class on
//       the variant itself, not as a sibling field on ModuleEntry::Def.
//       S69 Submission 36 promoted PlatformEffect from PrimitiveKind
//       sub-discriminator to its own DefKind variant; the substantive
//       Decision-26 invariant (variant-internal scheduling_class) is
//       preserved, restated at the DefKind level.
#[test]
fn def_kind_platform_effect_carries_scheduling_class() {
    // Build a platform-effect entry.
    let entry = mk_def(
        DefKind::PlatformEffect {
            scheduling_class: crate::SchedulingClass::Commutative,
            poll_shape: false,
            got_slot: 0,
            mode_summary: None,
        },
        None,
    );

    match entry {
        ModuleEntry::Def { kind, .. } => match *kind {
            DefKind::PlatformEffect {
                scheduling_class, ..
            } => {
                assert_eq!(
                    scheduling_class,
                    crate::SchedulingClass::Commutative,
                    "scheduling_class must be readable from the variant directly"
                );
            }
            other => panic!("expected DefKind::PlatformEffect {{ .. }}, got {:?}", other),
        },
        other => panic!("expected ModuleEntry::Def, got {:?}", other),
    }
}

// spec: design/arch/CLAUDE.md Sprint 66 Wave 0 amendment — `fn_ptr` field
//       removed from `ModuleEntry::Def`; `scheduling_class` inside
//       `DefKind::PlatformEffect` (S69 Submission 36 — promoted from
//       PrimitiveKind sub-variant) continues to round-trip via serde
//       (it is static manifest data, not a runtime pointer).
#[test]
fn platform_effect_scheduling_class_round_trips() {
    // Explicit `<()>` annotation: `code: None` is polymorphic in `C`, so
    // the inferred `C` would be ambiguous without context.
    let entry: ModuleEntry = ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::PlatformEffect {
            scheduling_class: crate::SchedulingClass::ResourceSerial,
            poll_shape: true,
            got_slot: 0,
            mode_summary: None,
        }),
        callees: Vec::new(),
        value_use: false,
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
    };

    let json = serde_json::to_string(&entry).expect("entry must serialize");

    // No leaked runtime pointer field of any name.
    assert!(
        !json.contains("fn_ptr"),
        "serialised form must not contain any `fn_ptr` field (the field has been removed entirely): {}",
        json
    );
    // jit_name retired per S69 Submission 36 — symbol-table key IS the
    // JIT linker name uniformly per src/CLAUDE.md §"JIT Symbol Names".
    assert!(
        !json.contains("jit_name"),
        "serialised form must not contain `jit_name` (retired S69 Submission 36): {}",
        json
    );

    let rt: ModuleEntry = serde_json::from_str(&json).expect("entry must deserialize");
    match rt {
        ModuleEntry::Def { kind, .. } => {
            // scheduling_class (on the variant) MUST round-trip — it is static
            // manifest data, not a runtime pointer.
            match *kind {
                DefKind::PlatformEffect {
                    scheduling_class,
                    poll_shape,
                    ..
                } => {
                    assert_eq!(
                        scheduling_class,
                        crate::SchedulingClass::ResourceSerial,
                        "scheduling_class inside DefKind::PlatformEffect must survive serde roundtrip"
                    );
                    // S94 R1 (FIXME 0457): poll_shape rides alongside and must
                    // survive serde too — it is the backend's poll-vs-blocking
                    // emission key.
                    assert!(
                        poll_shape,
                        "poll_shape inside DefKind::PlatformEffect must survive serde roundtrip"
                    );
                }
                other => panic!("expected DefKind::PlatformEffect, got {:?}", other),
            }
        }
        other => panic!("expected ModuleEntry::Def, got {:?}", other),
    }
}

// spec: design/arch/effect-concurrency.md §13 "S94 R1" (FIXME 0457) — the
//       `poll_shape` field is `#[serde(default)]`, and its default polarity is
//       chosen so a PRE-S94 cached `.meta.json` (whose serialized
//       `PlatformEffect` has no `poll_shape` key) deserializes as a v6 BLOCKING
//       effect (`poll_shape == false`). This is the cache-back-compat guard:
//       old caches keep their byte-identical blocking behaviour, no rebuild
//       forced by the field addition.
#[test]
fn platform_effect_poll_shape_defaults_to_false_for_pre_s94_cache() {
    // A pre-S94 serialized DefKind::PlatformEffect: externally-tagged enum with
    // the two fields that existed before the poll_shape addition. No poll_shape.
    let legacy_json = r#"{"PlatformEffect":{"scheduling_class":"Commutative","got_slot":3}}"#;
    let kind: DefKind =
        serde_json::from_str(legacy_json).expect("pre-S94 PlatformEffect must still deserialize");
    match kind {
        DefKind::PlatformEffect {
            scheduling_class,
            poll_shape,
            got_slot,
            mode_summary,
        } => {
            assert_eq!(scheduling_class, crate::SchedulingClass::Commutative);
            assert_eq!(got_slot, 3);
            assert!(
                !poll_shape,
                "a pre-S94 cache (no poll_shape key) MUST default to blocking (false)"
            );
            assert!(
                mode_summary.is_none(),
                "a pre-S102 cache (no mode_summary key) MUST default to None (Decision-24)"
            );
        }
        other => panic!("expected DefKind::PlatformEffect, got {:?}", other),
    }
}

// spec: design/arch/test-discovery.md §6/§7 — DefKind::PrimitiveExtern is a
//       payload-free unit variant (host-promised extern; key IS the ABI
//       name; slot-less; code None). Pins the serde round-trip alongside
//       the other DefKind variants. Post-S83 the slot-less invariant is
//       structural — PrimitiveExtern carries no slot field — so
//       callable_got_slot() is None by representation, not by a field value.
#[test]
fn def_kind_primitive_extern_round_trips() {
    // Explicit `<()>` annotation: `code: None` is polymorphic in `C`.
    let entry: ModuleEntry = ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::PrimitiveExtern),
        callees: Vec::new(),
        value_use: false,
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
    };

    // Slot-less is structural — there is no slot field on PrimitiveExtern.
    assert_eq!(
        entry.callable_got_slot(),
        None,
        "PrimitiveExtern is slot-less by representation"
    );

    let json = serde_json::to_string(&entry).expect("entry must serialize");
    let rt: ModuleEntry = serde_json::from_str(&json).expect("entry must deserialize");
    match rt {
        ModuleEntry::Def { kind, .. } => {
            assert!(
                matches!(*kind, DefKind::PrimitiveExtern),
                "kind must round-trip as PrimitiveExtern; got {:?}",
                kind
            );
        }
        other => panic!("expected ModuleEntry::Def, got {:?}", other),
    }
}

// ---- Sprint 58 Wave 2 Step 5a — Decision 33: structural-decl fields on SymbolTable ----

/// Build an `ImportSpec` with a unique span (used to verify source-order
/// preservation in the no-deduplication and ordering tests).
fn mk_import(module_path: &str, names: &[&str], span_start: u32) -> ImportSpec {
    ImportSpec {
        module_path: ModuleFullPath::from(module_path),
        alias: None,
        names: ImportNames::Specific(names.iter().map(|s| Symbol::from(*s)).collect()),
        span: Span::new(span_start, span_start + 8),
    }
}

/// Build an `ExportSpec` with a unique span.
fn mk_export(module_path: &str, names: &[&str], span_start: u32) -> ExportSpec {
    ExportSpec {
        module_path: ModuleFullPath::from(module_path),
        names: ImportNames::Specific(names.iter().map(|s| Symbol::from(*s)).collect()),
        span: Span::new(span_start, span_start + 8),
    }
}

/// Build a `PlatformSpec` with a unique span.
fn mk_platform(name: &str, span_start: u32) -> PlatformSpec {
    PlatformSpec {
        name: name.to_string(),
        span: Span::new(span_start, span_start + 8),
    }
}

/// Build a `ModDecl` with a unique span.
fn mk_mod(name: &str, visibility: Visibility, span_start: u32) -> ModDecl {
    ModDecl {
        name: ModuleName::from(name),
        visibility,
        inline_body: None,
        span: Span::new(span_start, span_start + 8),
    }
}

// spec: design/typecheck/ast-annotation.md §11.3 invariant 1 — source-order preservation
//       (importing `[a [x]]` then `[b [y]]` records both in declaration order).
#[test]
fn symbol_table_imports_preserves_source_order() {
    let mut st = SymbolTable::new(ModuleFullPath::from("user"));

    // Push three imports in source order; spans are strictly increasing.
    st.imports.push(mk_import("a", &["x"], 10));
    st.imports.push(mk_import("b", &["y"], 30));
    st.imports.push(mk_import("c", &["z"], 50));

    assert_eq!(st.imports.len(), 3, "all three imports must be recorded");

    // First-class structural shape: module paths in source order.
    assert_eq!(
        st.imports[0].module_path.as_ref(),
        "a",
        "imports[0] must be the first form pushed"
    );
    assert_eq!(st.imports[1].module_path.as_ref(), "b");
    assert_eq!(st.imports[2].module_path.as_ref(), "c");

    // Span ordering: insertion order matches source order.
    assert!(
        st.imports[0].span.start < st.imports[1].span.start,
        "source-order invariant: imports[0].span.start < imports[1].span.start"
    );
    assert!(
        st.imports[1].span.start < st.imports[2].span.start,
        "source-order invariant: imports[1].span.start < imports[2].span.start"
    );
}

// spec: design/typecheck/ast-annotation.md §11.3 invariant 2 — no deduplication
//       (importing `[a [x y]]` then `[a [x]]` records both; writer MUST NOT dedup).
#[test]
fn symbol_table_imports_no_deduplication() {
    let mut st = SymbolTable::new(ModuleFullPath::from("user"));

    // Two imports from the same module, different name lists, distinct spans.
    st.imports.push(mk_import("a", &["x", "y"], 10));
    st.imports.push(mk_import("a", &["x"], 30));

    assert_eq!(
        st.imports.len(),
        2,
        "duplicate imports MUST NOT collapse — both spans needed for resolver diagnostics"
    );

    // Both retain their distinct spans (not collapsed to one).
    assert_eq!(st.imports[0].span.start, 10);
    assert_eq!(st.imports[1].span.start, 30);

    // Same shape applies to structurally-identical pushes (different spans).
    let mut st2 = SymbolTable::new(ModuleFullPath::from("user"));
    st2.imports.push(mk_import("a", &["x"], 10));
    st2.imports.push(mk_import("a", &["x"], 30));
    assert_eq!(
        st2.imports.len(),
        2,
        "structurally-identical imports with distinct spans MUST NOT collapse"
    );
}

// spec: design/typecheck/ast-annotation.md §11.3 invariant 3 — no cross-module mixing
//       (module A's `imports` does not contain B's imports).
#[test]
fn symbol_table_no_cross_module_mixing() {
    // Two distinct symbol tables for modules A and B.
    let mut a = SymbolTable::new(ModuleFullPath::from("user.a"));
    let mut b = SymbolTable::new(ModuleFullPath::from("user.b"));

    // Push to A only.
    a.imports.push(mk_import("primitives", &["foo"], 10));
    a.exports.push(mk_export("user.a", &["bar"], 20));
    a.platforms.push(mk_platform("io", 30));
    a.submodules.push(mk_mod("inner", Visibility::Public, 40));

    // B is untouched.
    assert_eq!(
        b.imports.len(),
        0,
        "B's imports MUST be empty — A's writes do not leak"
    );
    assert_eq!(b.exports.len(), 0, "B's exports MUST be empty");
    assert_eq!(b.platforms.len(), 0, "B's platforms MUST be empty");
    assert_eq!(b.submodules.len(), 0, "B's submodules MUST be empty");

    // Now push to B; A is unchanged.
    b.imports.push(mk_import("primitives", &["baz"], 100));
    assert_eq!(a.imports.len(), 1, "A's imports unchanged after B's write");
    assert_eq!(b.imports.len(), 1);

    // Distinct content across modules.
    assert_ne!(
        a.imports[0].span.start, b.imports[0].span.start,
        "A and B carry independent records"
    );
}

// spec: design/typecheck/ast-annotation.md §11.3 invariant 4 — coherence with
//       ModuleEntry::Import chains is one-way (positive direction):
//       every imports entry's specific names have a corresponding ModuleEntry::Import.
//       The reverse is NOT required (implicit prelude injection is /int's call).
#[test]
fn symbol_table_imports_have_corresponding_module_entries_positive() {
    let mut st = SymbolTable::new(ModuleFullPath::from("user"));

    // Structural record: import [primitives [foo bar]].
    st.imports
        .push(mk_import("primitives", &["foo", "bar"], 10));

    // Resolved effects: per-symbol Import entries from the same module.
    st.insert(
        Symbol::from("foo"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("foo"),
            },
            visibility: Visibility::Private,
        },
    );
    st.insert(
        Symbol::from("bar"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from("bar"),
            },
            visibility: Visibility::Private,
        },
    );

    // For every name in every Specific imports entry, a corresponding
    // ModuleEntry::Import must exist whose source matches.
    for spec in &st.imports {
        if let ImportNames::Specific(syms) = &spec.names {
            for sym in syms {
                let entry = st.get(sym.as_ref()).unwrap_or_else(|| {
                    panic!(
                        "import [{} [{}]] has no corresponding ModuleEntry::Import for `{}`",
                        spec.module_path.as_ref(),
                        sym.as_ref(),
                        sym.as_ref()
                    )
                });
                match entry {
                    ModuleEntry::Import { source, .. } => {
                        assert_eq!(
                            source.module, spec.module_path,
                            "ModuleEntry::Import source module must match imports entry"
                        );
                        assert_eq!(
                            source.symbol.as_ref(),
                            sym.as_ref(),
                            "ModuleEntry::Import source symbol must match imports entry"
                        );
                    }
                    other => panic!(
                        "expected ModuleEntry::Import for `{}`, got {:?}",
                        sym.as_ref(),
                        other
                    ),
                }
            }
        }
    }

    // Reverse direction (every ModuleEntry::Import has an imports entry)
    // is /int's Wave 2b design call per §11.3 invariant 4 — NOT enforced
    // here. Implicit prelude injection produces ModuleEntry::Import chains
    // without a structural imports entry, and that may be the chosen
    // behaviour. /int picks based on resolver-diagnostic quality.
}

// spec: design/typecheck/ast-annotation.md §11.3 invariant 5 — read-only after
//       typecheck completes. There is no setter API for these fields; they are
//       written via direct field access by the worker (per §11.2). This test
//       is the documented-sense check: SymbolTable exposes no `set_imports`
//       /`add_import` / `clear_imports`-style mutator method that would imply
//       a public mutation protocol post-typecheck.
#[test]
fn symbol_table_structural_fields_have_no_setter_api() {
    // Compile-time enforcement: this test compiles only because no such
    // methods exist. The presence of any of the following inherent methods
    // would indicate an unintended mutation API and SHOULD break the build:
    //
    //   st.set_imports(...)
    //   st.add_import(...)
    //   st.clear_imports()
    //   st.set_exports(...)
    //   st.set_platforms(...)
    //   st.set_submodules(...)
    //
    // The fields are `pub`, so the worker writes via `st.imports.push(spec)`
    // directly — that is the documented writer protocol (§11.2). No setter
    // method abstraction is introduced because doing so would imply the
    // mutation is part of the type's public API; the actual contract is
    // "writer-only during the form-by-form classification pass, frozen
    // after `tc.check_program(...)` returns" (§11.3 invariant 5), which
    // is enforced at the call-site discipline level (in `/int`'s
    // `src/worker.rs`), not at the type level.
    //
    // Assert nothing additional here — the test passes by compilation.
    // Constructor returns empty fields, confirming the only mutation path
    // is direct field-access by the writer.
    let st = SymbolTable::new(ModuleFullPath::from("user"));
    assert!(
        st.imports.is_empty(),
        "fresh SymbolTable starts with empty imports"
    );
    assert!(
        st.exports.is_empty(),
        "fresh SymbolTable starts with empty exports"
    );
    assert!(
        st.platforms.is_empty(),
        "fresh SymbolTable starts with empty platforms"
    );
    assert!(
        st.submodules.is_empty(),
        "fresh SymbolTable starts with empty submodules"
    );
}

// spec: design/typecheck/ast-annotation.md §11.3 invariant 6 — serde round-trip
//       identity. A SymbolTable serialised → deserialised yields structurally
//       identical fields modulo runtime-only fields (`got`, `code`,
//       `linker`).
#[test]
fn symbol_table_serde_round_trip_with_structural_decls() {
    let mut st = SymbolTable::new(ModuleFullPath::from("user.module"));
    st.schema_version = 1;

    // Populate all four structural fields with non-trivial content.
    st.imports
        .push(mk_import("primitives", &["foo", "bar"], 10));
    st.imports.push(mk_import("user.helper", &["baz"], 30));

    st.exports
        .push(mk_export("user.module", &["public_fn"], 50));

    st.platforms.push(mk_platform("stdio", 70));
    st.platforms.push(mk_platform("test_capture", 90));

    st.submodules
        .push(mk_mod("public_child", Visibility::Public, 110));
    st.submodules
        .push(mk_mod("private_child", Visibility::Private, 130));

    // Also add one Def entry to confirm symbols round-trip alongside.
    st.insert(
        Symbol::from("entry"),
        mk_def(
            DefKind::UserFn {
                fn_state: UserFnState::NotDetermined,
            },
            Some(trivial_variant("entry")),
        ),
    );

    // Round-trip via serde-JSON.
    let json = serde_json::to_string(&st).expect("SymbolTable must serialize");
    let rt: SymbolTable = serde_json::from_str(&json).expect("SymbolTable must deserialize");

    // Structural identity on the four new fields.
    assert_eq!(rt.imports.len(), 2, "imports.len() must round-trip");
    assert_eq!(rt.imports[0].module_path.as_ref(), "primitives");
    assert_eq!(rt.imports[0].span.start, 10);
    assert_eq!(rt.imports[1].module_path.as_ref(), "user.helper");
    assert_eq!(rt.imports[1].span.start, 30);

    assert_eq!(rt.exports.len(), 1, "exports.len() must round-trip");
    assert_eq!(rt.exports[0].module_path.as_ref(), "user.module");
    assert_eq!(rt.exports[0].span.start, 50);

    assert_eq!(rt.platforms.len(), 2, "platforms.len() must round-trip");
    assert_eq!(rt.platforms[0].name, "stdio");
    assert_eq!(rt.platforms[1].name, "test_capture");
    assert_eq!(rt.platforms[0].span.start, 70);

    assert_eq!(rt.submodules.len(), 2, "submodules.len() must round-trip");
    assert_eq!(rt.submodules[0].name.as_ref(), "public_child");
    assert_eq!(
        rt.submodules[0].visibility,
        Visibility::Public,
        "visibility must round-trip (Public)"
    );
    assert_eq!(rt.submodules[1].name.as_ref(), "private_child");
    assert_eq!(
        rt.submodules[1].visibility,
        Visibility::Private,
        "visibility must round-trip (Private)"
    );

    // Schema version round-trips.
    assert_eq!(rt.schema_version, 1, "schema_version must round-trip");

    // Symbols round-trip (sanity check that adding new fields didn't
    // disturb the existing serde shape).
    assert!(rt.get("entry").is_some(), "Def entry must round-trip");

    // Source ordering invariant survives the round-trip.
    assert!(
        rt.imports[0].span.start < rt.imports[1].span.start,
        "source-order invariant survives serde round-trip"
    );
}

// spec: design/arch/CLAUDE.md Decision 34 + trait-impl-cache-carrier.md §6 —
//       `schema_version` defaults to 0 when the field is absent (the loader
//       compares to `CACHE_SCHEMA_VERSION` and rejects mismatches as stale),
//       but a PRE-CARRIER sidecar (no `written_trait_impls`, S119 schema < 24)
//       now fails AT PARSE: the carrier field has deliberately NO
//       #[serde(default)], so wholesale invalidation happens at the serde
//       boundary — a default-empty read would silently reproduce the 0869
//       defect.
#[test]
fn symbol_table_schema_version_defaults_to_zero_for_legacy_cache() {
    // The Sprint-57-era shape (no schema_version, no structural-decl Vecs,
    // no carrier field) is a HARD serde error post-S119 — rejected before any
    // version comparison can even run.
    let legacy_json = r#"{
        "path": "user",
        "symbols": {},
        "next_got_slot": 0
    }"#;
    assert!(
        serde_json::from_str::<SymbolTable>(legacy_json).is_err(),
        "a pre-carrier sidecar must fail at parse (wholesale invalidation)"
    );

    // With the required carrier field present, the #[serde(default)] fields
    // (schema_version + the four structural-decl Vecs) still default — the
    // Decision-34 version-mismatch path for sidecars that ARE parseable.
    let carrier_json = r#"{
        "path": "user",
        "symbols": {},
        "next_got_slot": 0,
        "written_trait_impls": []
    }"#;
    let rt: SymbolTable = serde_json::from_str(carrier_json)
        .expect("carrier-bearing SymbolTable JSON must deserialize cleanly");
    assert_eq!(
        rt.schema_version, 0,
        "schema_version MUST default to 0 when absent — the loader detects \
         the mismatch against CACHE_SCHEMA_VERSION and rejects as stale"
    );
    assert!(rt.imports.is_empty(), "missing `imports` defaults to empty");
    assert!(rt.exports.is_empty(), "missing `exports` defaults to empty");
    assert!(rt.platforms.is_empty(), "missing `platforms` defaults to empty");
    assert!(
        rt.submodules.is_empty(),
        "missing `submodules` defaults to empty"
    );
}

// spec: design/typecheck/ast-annotation.md §11.3 invariant 2 — no deduplication
//       (same shape applies to exports as to imports).
#[test]
fn symbol_table_exports_no_deduplication() {
    let mut st = SymbolTable::new(ModuleFullPath::from("user"));

    st.exports.push(mk_export("user", &["foo"], 10));
    st.exports.push(mk_export("user", &["foo"], 30));

    assert_eq!(
        st.exports.len(),
        2,
        "duplicate exports MUST NOT collapse (parallel to imports invariant)"
    );
    assert_eq!(st.exports[0].span.start, 10);
    assert_eq!(st.exports[1].span.start, 30);
}

// ---- Sprint 58 Wave 3a — Decision 32: CodeStore / LinkerStore marker traits ----

// spec: design/typecheck/ast-annotation.md §12.1 + Decision 32 —
//       SymbolTable<C: CodeStore = (), L: LinkerStore = ()> defaults
//       resolve to SymbolTable<(), ()> when constructed without args.
//       Confirms the "default-(): propagation" invariant: typecheck-side
//       call sites that name `SymbolTable` (no args) get the unit
//       parameterisation and the `code: Option<()>` / `linker: Option<()>`
//       shape compiles cleanly.
#[test]
fn symbol_table_default_generics_resolve_to_unit() {
    // Construct via the inherent `SymbolTable<(), ()>::new(...)` path
    // (the only one defined; see the inherent-impl rationale on
    // `impl SymbolTable<(), ()>` for why `::new` lives there rather
    // than on the generic impl).
    let st = SymbolTable::new(ModuleFullPath::from("user"));

    // Annotate explicitly to assert the inferred parameterisation is
    // <(), ()>. The `:` binds a fresh local with the spelled type;
    // the assignment from `st` would fail to compile if the parameters
    // were anything other than <(), ()>.
    let _typed: SymbolTable<(), ()> = st;

    // The four Vec<…> fields and the linker / schema_version fields
    // are all populated with their defaults by `::new`. The `linker`
    // field is `Option<()>` (a meaningless tag from typecheck's POV);
    // confirm it starts as None.
    let st: SymbolTable<(), ()> = SymbolTable::new(ModuleFullPath::from("user"));
    assert!(
        st.linker.is_none(),
        "fresh SymbolTable<(), ()> must have linker: None (Wave 3a default)"
    );
    // Sanity: the structural-decl Vec<…> fields are empty too (Step 5a
    // invariant; reasserted here to prove parameterisation didn't
    // disturb the existing field set).
    assert!(st.imports.is_empty());
    assert!(st.exports.is_empty());
    assert!(st.platforms.is_empty());
    assert!(st.submodules.is_empty());
    // `code` field shape exists on every Def entry; it is Option<()>
    // for typecheck-side fixtures and would be Option<Code> for
    // integration-layer fixtures (Wave 3b instantiates `C = Code`).
}

// spec: design/typecheck/ast-annotation.md §12.2 + Decision 32 —
//       The blanket `impl<T: Send + Sync + 'static> CodeStore for T` /
//       `impl<T: Send + Sync + 'static> LinkerStore for T` makes both
//       traits trivially satisfied by `()` (zero-sized, Send + Sync +
//       'static) and by other common types the integration layer
//       might choose. Confirms the "no per-call-site impl line"
//       ergonomic property of the empty-marker design (Decision 32
//       rationale).
#[test]
fn code_store_and_linker_store_blanket_impl_holds() {
    // Compile-time check: the function below requires its parameter
    // type to satisfy `CodeStore`. The fact that this compiles is the
    // assertion — calling it with `()` and several other plausible
    // integration-layer concrete types proves the blanket impl
    // applies.
    fn _requires_code_store<T: CodeStore>() {}
    fn _requires_linker_store<T: LinkerStore>() {}

    _requires_code_store::<()>();
    _requires_linker_store::<()>();

    // Common Arc-wrapped shapes that the integration layer may use
    // for `C` (per Decision 35: `Arc<Jit>`-or-`Code`-enum) and `L`
    // (per Decision 35: `Arc<Linker>` if `L` is reactivated). Use
    // `Arc<()>` and `Arc<u64>` as stand-ins for the integration
    // layer's concrete shapes — they must satisfy the bound for the
    // Wave 3b instantiation to compile. `i64` exercises the simplest
    // primitive case (the §G.12 unit test for `module_entry_def_code_field_is_optional_c`
    // uses `i64` synthetically).
    _requires_code_store::<std::sync::Arc<()>>();
    _requires_code_store::<std::sync::Arc<u64>>();
    _requires_code_store::<i64>();
    _requires_code_store::<u64>();
    _requires_linker_store::<std::sync::Arc<()>>();
    _requires_linker_store::<std::sync::Arc<u64>>();

    // (Sprint 58 Wave 3b: the previous `_requires_code_store::<crate::Code>()`
    // assertion targeted the now-dissolved `cranelisp_types::Code` struct.
    // The replacement test lives in `src/code.rs::tests` —
    // `session_symbol_table_concrete_type_choice` — and asserts
    // `_requires_code_store::<src::code::Code>()` against the integration
    // layer's enum, the actual concrete type for `C`. This module's
    // tests stay strictly within `cranelisp-types`'s scope and exercise
    // only synthetic / `()`-flavoured shapes.)
}

// spec: design/typecheck/ast-annotation.md §12.4 + Decision 32 + §G.12
//       (`module_entry_def_code_field_is_optional_c`) —
//       `ModuleEntry<C>` parameterises the `code: Option<C>` field over
//       the `C: CodeStore` parameter. With a synthetic `C = i64`,
//       constructing `Def { code: Some(42i64), .. }` must compile and
//       round-trip via serde with `code` skipped (the serialised JSON
//       contains no `code` field; deserialise produces `code: None`
//       regardless of the source `C`).
#[test]
fn module_entry_def_code_field_is_optional_c() {
    // Synthetic `C = i64`: any `Send + Sync + 'static` type satisfies
    // CodeStore via the blanket impl. The point of this test is to
    // exercise the `Option<C>` parameterisation with a `C` that is
    // NOT `Code` and NOT `()` — proving the field is genuinely
    // generic over the parameter, not specialised to either default.
    let entry: ModuleEntry<i64> = ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::UserFn {
            fn_state: UserFnState::NotDetermined,
        }),
        callees: Vec::new(),
        value_use: false,
        trait_origin: None,
        seq: 0,
        ast: Some(trivial_variant("synthetic")),
        codegen_view: None,
        code: Some(42i64),
    };

    // The `code` field carries the synthetic `C = i64` value.
    match &entry {
        ModuleEntry::Def { code, .. } => {
            assert_eq!(
                *code,
                Some(42i64),
                "code field must hold the constructed Some(42i64)"
            );
        }
        other => panic!("expected ModuleEntry::Def, got {:?}", other),
    }

    // Serde discipline: `code` is `#[serde(skip)]`, so the serialised
    // shape MUST NOT contain a `code` field, and the deserialised
    // entry MUST have `code: None` regardless of the source `C`. Use
    // the `()` flavour for the deserialise target (typecheck-side
    // view) to confirm cross-flavour serde compatibility — the
    // serialised shape is identical because `code` never appears in
    // the JSON.
    let json = serde_json::to_string(&entry).expect("ModuleEntry<i64> must serialize");
    assert!(
        !json.contains("\"code\""),
        "serialised form must not contain the `code` field (it is #[serde(skip)]): {}",
        json
    );

    let rt: ModuleEntry<()> = serde_json::from_str(&json)
        .expect("ModuleEntry<()> must deserialize from ModuleEntry<i64>'s JSON");
    match rt {
        ModuleEntry::Def { code, ast, .. } => {
            // The deserialised `code` is `None::<()>` — the source
            // `Some(42i64)` did not survive (correctly) because the
            // field is skipped.
            assert!(
                code.is_none(),
                "deserialised ModuleEntry<()>::Def must have code: None (serde(skip)); got {:?}",
                code
            );
            // ast survives the round-trip — only the `code` field is
            // skipped (the prior `fn_ptr` field has been removed entirely
            // per the Sprint 66 Wave 0 amendment).
            assert!(ast.is_some(), "ast must survive the round-trip");
        }
        other => panic!("expected ModuleEntry::Def, got {:?}", other),
    }
}

// ---- Tier-1 DefBuilder (ModuleEntry::def) ----

fn mono_scheme(ty: Type) -> Scheme {
    Scheme {
        type_vars: vec![],
        constraints: HashMap::new(),
        ty,
    }
}

// spec: design/arch/fixmes/0241 — Tier-1 Def constructor: defaults
#[test]
fn def_builder_defaults() {
    // Use a slot-less kind so the builder's field defaults (not a kind
    // slot) are the subject — the GOT slot now rides on the kind (S83), so
    // there is no flat `got_slot` field to default.
    let entry: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Int),
        DefKind::UserFn {
            fn_state: UserFnState::NotDetermined,
        },
    )
    .build();
    // No callable slot by default (NotDetermined is slot-less).
    assert_eq!(
        entry.callable_got_slot(),
        None,
        "default builder yields no callable slot"
    );
    match entry {
        ModuleEntry::Def {
            scheme,
            visibility,
            docstring,
            param_names,
            kind,
            callees,
            value_use,
            trait_origin,
            seq,
            ast,
            codegen_view,
            code,
        } => {
            assert_eq!(scheme.ty, Type::Int);
            assert_eq!(
                visibility,
                Visibility::Public,
                "default visibility is Public"
            );
            assert!(docstring.is_none());
            assert!(param_names.is_empty());
            assert!(matches!(
                *kind,
                DefKind::UserFn {
                    fn_state: UserFnState::NotDetermined
                }
            ));
            assert!(callees.is_empty(), "callees defaulted, never settable");
            assert!(
                !value_use,
                "value_use defaulted false, never settable at build"
            );
            assert!(trait_origin.is_none());
            assert_eq!(seq, 0);
            assert!(ast.is_none());
            assert!(
                codegen_view.is_none(),
                "codegen_view defaulted, never settable via build()"
            );
            assert!(code.is_none(), "code defaulted, never settable");
        }
        other => panic!("expected Def, got {:?}", other),
    }
}

// spec: design/arch/fixmes/0241 — Tier-1 Def constructor: overrides
#[test]
fn def_builder_overrides() {
    let trait_name = FQTraitName::new(ModuleFullPath::from("core.num"), TraitName::from("Num"));
    // The GOT slot rides on the kind (S83): a concrete callable carries it
    // via `UserFnState::Concrete { got_slot }`. The builder has no
    // `.got_slot(_)` setter — the slot is part of the `kind` value passed in.
    let entry: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Bool),
        DefKind::UserFn {
            fn_state: UserFnState::Concrete {
                got_slot: 7,
                mode_summary: None,
            },
        },
    )
    .visibility(Visibility::Private)
    .docstring("doc")
    .param_names(vec![Symbol::from("a"), Symbol::from("b")])
    .trait_origin(trait_name.clone())
    .seq(42)
    .ast(trivial_variant("f"))
    .build();
    assert_eq!(
        entry.callable_got_slot(),
        Some(7),
        "concrete callable slot rides on the kind"
    );
    match entry {
        ModuleEntry::Def {
            visibility,
            docstring,
            param_names,
            trait_origin,
            seq,
            ast,
            ..
        } => {
            assert_eq!(visibility, Visibility::Private);
            assert_eq!(docstring.as_deref(), Some("doc"));
            assert_eq!(param_names, vec![Symbol::from("a"), Symbol::from("b")]);
            assert_eq!(trait_origin, Some(trait_name));
            assert_eq!(seq, 42);
            assert!(ast.is_some());
        }
        other => panic!("expected Def, got {:?}", other),
    }
}

// spec: design/arch/fixmes/0241 — From<DefBuilder> conversion (terminal)
#[test]
fn def_builder_from_conversion() {
    let entry: ModuleEntry = ModuleEntry::def(mono_scheme(Type::Int), DefKind::primitive(0)).into();
    assert!(matches!(entry, ModuleEntry::Def { .. }));
}

// =============================================================================
// S102 CS-A — ownership carrier accessors + the FIXME-0476 PrimitiveBody shape
// (design/arch/ownership-inference.md §3.3;
//  design/typecheck/ownership-inference.md §13.1 items 6, 10, 11)
// =============================================================================

// spec: design/arch/fixmes/0476 §Ruling — an Inline primitive is slot-less BY
//       CONSTRUCTION; callable_got_slot() answers None structurally, and
//       is_callable_target() still answers true (the resolution stop
//       condition covers slot-dispatched AND inline-dispatched kinds).
#[test]
fn inline_primitive_is_slotless_but_callable_target() {
    let inline: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Int),
        DefKind::Primitive {
            body: PrimitiveBody::Inline,
            mode_summary: None,
        },
    )
    .build();
    assert_eq!(
        inline.callable_got_slot(),
        None,
        "Inline carries no slot by construction"
    );
    assert!(
        inline.is_callable_target(),
        "Inline IS a dispatchable call target (inline emission)"
    );

    let ext: ModuleEntry = ModuleEntry::def(mono_scheme(Type::Int), DefKind::primitive(5)).build();
    assert_eq!(ext.callable_got_slot(), Some(5));
    assert!(ext.is_callable_target());
}

// spec: design/arch/fixmes/0476 §Ruling — is_callable_target() preserves the
//       negative half of the stop condition: non-callable kinds are NOT
//       callable targets (shadowing precedence unchanged).
#[test]
fn non_callable_kinds_are_not_callable_targets() {
    let template: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Int),
        DefKind::UserFn {
            fn_state: UserFnState::NotDetermined,
        },
    )
    .build();
    assert!(!template.is_callable_target());

    let ext_prim: ModuleEntry =
        ModuleEntry::def(mono_scheme(Type::Int), DefKind::PrimitiveExtern).build();
    assert!(
        !ext_prim.is_callable_target(),
        "PrimitiveExtern dispatches by-name, never a target"
    );
}

// spec: design/typecheck/ownership-inference.md §13.1 item 6 — uniform
//       mode_summary() read + set_mode_summary() did-write mutator on the
//       callable kinds; non-callable kinds answer None / false (no summary
//       slot by construction).
#[test]
fn mode_summary_accessor_and_mutator_cover_callable_kinds() {
    use crate::{Mode, ModeSummary};
    let summary = ModeSummary {
        param_modes: vec![Mode::Borrowed],
        ..Default::default()
    };

    // UserFn Concrete: writable, readable.
    let mut concrete: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Int),
        DefKind::UserFn {
            fn_state: UserFnState::Concrete {
                got_slot: 1,
                mode_summary: None,
            },
        },
    )
    .build();
    assert!(
        concrete.mode_summary().is_none(),
        "pre-analysis entry carries no summary"
    );
    assert!(
        concrete.set_mode_summary(Some(summary.clone())),
        "Concrete is a publication target"
    );
    assert_eq!(concrete.mode_summary(), Some(&summary));

    // Primitive: the SAME slot carries declared facts (item 7 — no separate type).
    let mut prim: ModuleEntry =
        ModuleEntry::def(mono_scheme(Type::Int), DefKind::primitive(0)).build();
    assert!(prim.set_mode_summary(Some(summary.clone())));
    assert_eq!(prim.mode_summary(), Some(&summary));

    // Non-callable kind: did-not-write indicator, still None.
    let mut nd: ModuleEntry = ModuleEntry::def(
        mono_scheme(Type::Int),
        DefKind::UserFn {
            fn_state: UserFnState::NotDetermined,
        },
    )
    .build();
    assert!(
        !nd.set_mode_summary(Some(summary)),
        "no summary slot on non-callable kinds"
    );
    assert!(nd.mode_summary().is_none());
}

// spec: design/typecheck/ownership-inference.md §13.1 item 10 /
//       §8.3 — the per-entry value-use mark: builder-defaulted false,
//       pass-written via set_value_use (did-write for Def entries only).
#[test]
fn value_use_mark_defaults_false_and_is_pass_written() {
    let mut entry: ModuleEntry =
        ModuleEntry::def(mono_scheme(Type::Int), DefKind::primitive(0)).build();
    assert!(
        !entry.value_use(),
        "builder default is false (pre-analysis point)"
    );
    assert!(entry.set_value_use(true));
    assert!(entry.value_use());

    let mut imp: ModuleEntry = ModuleEntry::Import {
        source: FQSymbol {
            module: ModuleFullPath::from("m"),
            symbol: Symbol::from("x"),
        },
        visibility: Visibility::Public,
    };
    assert!(!imp.set_value_use(true), "non-Def entries carry no mark");
    assert!(!imp.value_use());
}

// spec: design/arch/ownership-inference.md §3.3 — serde strict-additivity: a
//       pre-S102 Primitive JSON (bare got_slot shape) does NOT deserialize
//       against the reshaped variant; the CACHE_SCHEMA_VERSION 11→12 bump is
//       what rejects such caches wholesale (this pins that the reshape is
//       non-additive, i.e. the bump is mandatory), while the NEW shape with
//       absent mode_summary/borrowed_sibling_slot defaults conservatively.
#[test]
fn primitive_reshape_serde_shape() {
    // Old v11 shape must NOT silently deserialize (field renamed to `body`).
    let legacy = r#"{"Primitive":{"got_slot":3}}"#;
    assert!(
        serde_json::from_str::<DefKind>(legacy).is_err(),
        "pre-S102 Primitive shape must not deserialize — schema bump covers it"
    );
    // New shape with only the mandatory Extern slot: sibling + summary default.
    let v12 = r#"{"Primitive":{"body":{"Extern":{"got_slot":3}}}}"#;
    match serde_json::from_str::<DefKind>(v12).expect("v12 shape deserializes") {
        DefKind::Primitive {
            body:
                PrimitiveBody::Extern {
                    got_slot,
                    borrowed_sibling_slot,
                },
            mode_summary,
        } => {
            assert_eq!(got_slot, 3);
            assert!(
                borrowed_sibling_slot.is_none(),
                "absent sibling defaults None"
            );
            assert!(
                mode_summary.is_none(),
                "absent declared facts default None (Decision-24)"
            );
        }
        other => panic!("expected Extern Primitive, got {other:?}"),
    }
}

// ---- S111 R7 — GOT slot exhaustion is a diagnosed error, not release UB ----

// spec: 12-runtime §12.2 — GOT exhaustion boundary (GE-1)
// The GOT slab is a fixed `GOT_TABLE_SIZE` array; `allocate_got_slot` hands out
// `Ok(0)..=Ok(GOT_TABLE_SIZE-1)` and then refuses with `Err(GotExhausted)` — the
// diagnosed replacement for the former unchecked `+= 1` (release slot-1024 UB).
// Failure is idempotent: `next_got_slot` is NOT advanced, so a second call fails
// identically.
#[test]
fn got_slot_exhaustion_boundary() {
    let mut st = SymbolTable::new(ModuleFullPath::from("user"));

    // 1024 consecutive allocations succeed with the monotone slot indices.
    for expected in 0..crate::GOT_TABLE_SIZE {
        match st.allocate_got_slot() {
            Ok(slot) => assert_eq!(slot, expected, "slot {expected} must allocate in order"),
            Err(e) => panic!("slot {expected} must be Ok, got {e:?}"),
        }
    }

    // The 1025th call is refused, carrying the exhausted module.
    let first = st.allocate_got_slot();
    match &first {
        Err(GotExhausted { module }) => {
            assert_eq!(module, &ModuleFullPath::from("user"), "carries the module");
        }
        Ok(slot) => panic!("slot {slot} past the slab bound must be Err(GotExhausted)"),
    }

    // Idempotent failure — `next_got_slot` was not advanced, so a second call
    // fails identically (stable, repeatable; no bump on failure).
    let second = st.allocate_got_slot();
    assert_eq!(first, second, "exhaustion failure is stable and repeatable");
    assert_eq!(
        st.next_got_slot,
        crate::GOT_TABLE_SIZE,
        "next_got_slot must NOT advance past the bound on failure"
    );
}

// spec: 12-runtime §12.2 — GOT exhaustion diagnostic content (GE-2)
// The error names the module AND the capacity, so the caller-mapped compile
// error is self-explanatory without re-deriving either.
#[test]
fn got_slot_exhaustion_diagnostic_names_module_and_capacity() {
    let mut st = SymbolTable::new(ModuleFullPath::from("proj.widget"));
    for _ in 0..crate::GOT_TABLE_SIZE {
        st.allocate_got_slot().expect("within-bounds allocation");
    }
    let err = st.allocate_got_slot().expect_err("must be exhausted");
    let text = err.to_string();
    assert!(
        text.contains("proj.widget"),
        "diagnostic names the module: {text}"
    );
    assert!(
        text.contains(&crate::GOT_TABLE_SIZE.to_string()),
        "diagnostic names the capacity: {text}"
    );
}

// spec: appendix-c-nfr §C.1.4 — per-type drop glue must have a stable,
// collision-free callable identity. Implementation lock: design/backend/
// transitive-drop-glue.md §3.1.
#[test]
fn drop_glue_names_are_injective_and_linker_safe() {
    let m = ModuleFullPath::from("user.mod");
    let n = FQTypeName::new(ModuleFullPath::from("p"), TypeName::from("Vec"));
    let cases = [
        drop_glue_symbol_name(&m, &ConcreteType::Int),
        drop_glue_symbol_name(&m, &ConcreteType::Bool),
        drop_glue_symbol_name(&m, &ConcreteType::ADT(n.clone(), vec![ConcreteType::Int])),
        drop_glue_symbol_name(&m, &ConcreteType::ADT(n, vec![ConcreteType::String])),
        drop_glue_symbol_name(
            &m,
            &ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Bool)),
        ),
        drop_glue_symbol_name(&ModuleFullPath::from("user_mod"), &ConcreteType::Int),
    ];
    let unique = cases
        .iter()
        .map(AsRef::<str>::as_ref)
        .collect::<std::collections::HashSet<_>>();
    assert_eq!(unique.len(), cases.len());
    assert!(
        cases
            .iter()
            .all(|n| n.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'))
    );
}

// spec: appendix-c-nfr §C.1.4 — recursive field structure determines the
// per-type drop glue. Implementation lock: design/backend/
// transitive-drop-glue.md §3.2.
#[test]
fn drop_glue_name_preserves_nested_concrete_structure() {
    let node = FQTypeName::new(ModuleFullPath::from("tree"), TypeName::from("Node"));
    let shallow = ConcreteType::ADT(node.clone(), vec![ConcreteType::String]);
    let deep = ConcreteType::ADT(
        node.clone(),
        vec![ConcreteType::ADT(node, vec![shallow.clone()])],
    );
    let m = ModuleFullPath::from("emit");
    assert_ne!(
        drop_glue_symbol_name(&m, &shallow),
        drop_glue_symbol_name(&m, &deep)
    );
    assert_eq!(
        drop_glue_symbol_name(&m, &deep),
        drop_glue_symbol_name(&m, &deep)
    );
}

// spec: appendix-c-nfr §C.1.4 — distinct concrete types require distinct
// per-type drop glue. Implementation lock: design/backend/
// transitive-drop-glue.md §3.1.
#[test]
fn drop_glue_name_length_prefixes_identifier_bytes() {
    let a = ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("a/b"), TypeName::from("C_D")),
        vec![],
    );
    let b = ConcreteType::ADT(
        FQTypeName::new(ModuleFullPath::from("a"), TypeName::from("b/C_D")),
        vec![],
    );
    assert_ne!(
        drop_glue_symbol_name(&ModuleFullPath::from("μ"), &a),
        drop_glue_symbol_name(&ModuleFullPath::from("μ"), &b)
    );
}

// spec: appendix-c-nfr §C.1.4 — distinct concrete function types require
// distinct per-type drop glue. Implementation lock: design/backend/
// transitive-drop-glue.md §3.1 (arity and params/result boundaries).
#[test]
fn drop_glue_name_separates_fn_arity_and_result_boundary() {
    let module = ModuleFullPath::from("emit");
    let one_param = ConcreteType::Fn(vec![ConcreteType::Int], Box::new(ConcreteType::Bool));
    let two_params = ConcreteType::Fn(
        vec![ConcreteType::Int, ConcreteType::Bool],
        Box::new(ConcreteType::String),
    );
    let nested_result = ConcreteType::Fn(
        vec![ConcreteType::Int],
        Box::new(ConcreteType::Fn(
            vec![ConcreteType::Bool],
            Box::new(ConcreteType::String),
        )),
    );

    assert_ne!(
        drop_glue_symbol_name(&module, &one_param),
        drop_glue_symbol_name(
            &module,
            &ConcreteType::Fn(
                vec![ConcreteType::Int, ConcreteType::Bool],
                Box::new(ConcreteType::Bool),
            ),
        ),
        "Fn parameter arity must distinguish otherwise shared leaves"
    );
    assert_ne!(
        drop_glue_symbol_name(&module, &two_params),
        drop_glue_symbol_name(&module, &nested_result),
        "a second parameter cannot collide with a nested result parameter"
    );
    assert_eq!(
        drop_glue_symbol_name(&module, &nested_result),
        drop_glue_symbol_name(&module, &nested_result),
        "equal complete function types must retain equal identity"
    );
}

// spec: appendix-c-nfr §C.1.4 — distinct nested concrete ADTs require
// distinct per-type drop glue. Implementation lock: design/backend/
// transitive-drop-glue.md §3.1 (nested ADT arity boundaries).
#[test]
fn drop_glue_name_separates_nested_adt_argument_boundaries() {
    let module = ModuleFullPath::from("emit");
    let pair = FQTypeName::new(ModuleFullPath::from("data"), TypeName::from("Pair"));
    let boxed = FQTypeName::new(ModuleFullPath::from("data"), TypeName::from("Box"));
    let outer_two_args = ConcreteType::ADT(
        pair.clone(),
        vec![
            ConcreteType::ADT(boxed.clone(), vec![ConcreteType::Int]),
            ConcreteType::Bool,
        ],
    );
    let nested_two_args = ConcreteType::ADT(
        pair,
        vec![ConcreteType::ADT(
            boxed,
            vec![ConcreteType::Int, ConcreteType::Bool],
        )],
    );

    assert_ne!(
        drop_glue_symbol_name(&module, &outer_two_args),
        drop_glue_symbol_name(&module, &nested_two_args),
        "outer and nested ADT argument boundaries must not flatten together"
    );
    assert_eq!(
        drop_glue_symbol_name(&module, &outer_two_args),
        drop_glue_symbol_name(&module, &outer_two_args),
        "equal nested ADTs must retain equal identity"
    );
}

// ---- CallableSlot witness mint (S119 types-first slice;
// design/arch/concreteness-types-first.md §3.1/§3.2) ----

fn generic_scheme(ty: Type, vars: Vec<crate::TypeId>) -> Scheme {
    Scheme {
        type_vars: vars,
        constraints: HashMap::new(),
        ty,
    }
}

// spec: design/arch/concreteness-types-first.md §3.2 — the mint refuses a
// non-concrete scheme (the planted fault: a `∀a. a→a` template must not
// acquire a slot).
#[test]
fn mint_refuses_non_concrete_scheme() {
    let mut st = SymbolTable::new(ModuleFullPath::from("m"));
    let poly = generic_scheme(
        Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
        vec![0],
    );
    let err = st
        .mint_callable_slot(&poly)
        .expect_err("non-concrete scheme must refuse");
    assert!(
        matches!(err, SlotMintError::NotConcrete(crate::NotConcrete::Var(0))),
        "refusal carries the residual var: {err:?}"
    );
    // The refusal is side-effect-free: the cursor did not advance.
    assert_eq!(st.next_got_slot, 0, "refusal must not consume a slot");
}

// spec: design/arch/concreteness-types-first.md §3.2 — the negative leg: a
// concrete scheme mints, slots are monotone from 0, and the witness index
// matches the cursor the allocation consumed.
#[test]
fn mint_accepts_concrete_scheme_monotonically() {
    let mut st = SymbolTable::new(ModuleFullPath::from("m"));
    let conc = mono_scheme(Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    let a = st.mint_callable_slot(&conc).expect("concrete scheme mints");
    let b = st.mint_callable_slot(&conc).expect("concrete scheme mints");
    assert_eq!(a.index(), 0);
    assert_eq!(b.index(), 1);
    assert_eq!(st.next_got_slot, 2);
}

// spec: design/arch/concreteness-types-first.md §3.2 — a TyConApp head is
// non-concrete at the mint gate (same acceptance set as Type::is_concrete()).
#[test]
fn mint_refuses_hkt_head() {
    let mut st = SymbolTable::new(ModuleFullPath::from("m"));
    let hkt = generic_scheme(Type::TyConApp(4, vec![Type::Int]), vec![4]);
    let err = st.mint_callable_slot(&hkt).expect_err("HKT head refuses");
    assert!(matches!(
        err,
        SlotMintError::NotConcrete(crate::NotConcrete::HktHead(4))
    ));
}

// spec: design/arch/concreteness-types-first.md §3.2 — exhaustion surfaces as
// SlotMintError::Exhausted with the pre-existing GotExhausted meaning.
#[test]
fn mint_surfaces_got_exhaustion() {
    let mut st = SymbolTable::new(ModuleFullPath::from("m"));
    st.next_got_slot = GOT_TABLE_SIZE;
    let conc = mono_scheme(Type::Int);
    let err = st.mint_callable_slot(&conc).expect_err("slab exhausted");
    assert!(matches!(err, SlotMintError::Exhausted(_)));
    assert_eq!(
        st.next_got_slot, GOT_TABLE_SIZE,
        "exhaustion is stable and repeatable"
    );
}

// spec: design/arch/concreteness-types-first.md §3.1 — rebind (the
// Decision-31 REPL slot carry-forward) re-checks concreteness: transfer to a
// concrete redefinition succeeds and preserves the index; transfer to a
// non-concrete redefinition refuses.
#[test]
fn rebind_rechecks_concreteness() {
    let mut st = SymbolTable::new(ModuleFullPath::from("m"));
    let conc = mono_scheme(Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    let slot = st.mint_callable_slot(&conc).expect("mint");

    let conc2 = mono_scheme(Type::Fn(vec![Type::Bool], Box::new(Type::Int)));
    let rebound = slot.rebind(&conc2).expect("concrete rebind succeeds");
    assert_eq!(rebound.index(), slot.index(), "rebind preserves the index");

    let poly = generic_scheme(Type::Fn(vec![Type::Var(9)], Box::new(Type::Var(9))), vec![9]);
    let err = rebound
        .rebind(&poly)
        .expect_err("non-concrete rebind refuses");
    assert!(matches!(err, crate::NotConcrete::Var(9)));
}

// spec: design/arch/concreteness-types-first.md §3.6 — the wire pin:
// CallableSlot is #[serde(transparent)], so the serialized form is the bare
// index (byte-identical to the usize it will replace at the S120 flip — the
// retype alone forces no schema bump).
#[test]
fn callable_slot_serde_is_transparent() {
    let mut st = SymbolTable::new(ModuleFullPath::from("m"));
    let slot = st
        .mint_callable_slot(&mono_scheme(Type::Int))
        .expect("mint");
    let json = serde_json::to_string(&slot).expect("serialize");
    assert_eq!(json, "0", "wire shape is the bare index");
    let rt: CallableSlot = serde_json::from_str("17").expect("deserialize");
    assert_eq!(rt.index(), 17, "serde bypasses the mint — the cache load \
        boundary re-checks restored slots (R-29)");
}

// spec: design/arch/concreteness-types-first.md §3.3 — the DORMANT CtorState
// sum's wire shape, pinned ahead of the 0931 flip so the schema-window review
// diffs against a recorded shape.
#[test]
fn ctor_state_serde_shape_pin() {
    let template = CtorState::Template;
    assert_eq!(
        serde_json::to_string(&template).expect("serialize"),
        "\"Template\""
    );
    let mut st = SymbolTable::new(ModuleFullPath::from("m"));
    let slot = st
        .mint_callable_slot(&mono_scheme(Type::Int))
        .expect("mint");
    let concrete = CtorState::Concrete { got_slot: slot };
    assert_eq!(
        serde_json::to_string(&concrete).expect("serialize"),
        "{\"Concrete\":{\"got_slot\":0}}"
    );
    let rt: CtorState =
        serde_json::from_str("{\"Concrete\":{\"got_slot\":3}}").expect("deserialize");
    assert_eq!(rt, CtorState::Concrete { got_slot: rt_slot(3) });

    fn rt_slot(n: usize) -> CallableSlot {
        serde_json::from_str(&n.to_string()).expect("transparent slot")
    }
}

// ---- Injective GOT data-symbol mint (S119, FIXME 0748; safety-register R4) ----

/// Test-only decoder for the escape image — unambiguous decode IS the
/// injectivity argument: every `_` in the image begins exactly one legal pair.
fn decode_got_flat(flat: &str) -> Option<String> {
    let mut out = String::new();
    let mut chars = flat.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '_' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            '_' => out.push('_'),
            'd' => out.push('.'),
            'h' => out.push('-'),
            'u' => {
                let hex: String = (0..6).map(|_| chars.next()).collect::<Option<String>>()?;
                out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
            }
            _ => return None, // illegal pair — not in the image
        }
    }
    Some(out)
}

fn got_flat(path: &str) -> String {
    got_data_symbol_name(&ModuleFullPath::from(path))
        .strip_prefix("__cranelisp_got_")
        .expect("prefix")
        .to_string()
}

// spec: design/arch/safety-invariants.md §4 R4 — the collision class is closed:
// `a.b` and `a_b` mint DISTINCT GOT slab symbols (the inverted 0748 witness).
#[test]
fn got_data_symbol_name_is_injective_on_the_0748_pair() {
    assert_ne!(
        got_data_symbol_name(&ModuleFullPath::from("a.b")),
        got_data_symbol_name(&ModuleFullPath::from("a_b")),
    );
}

// spec: design/arch/fixmes/0748 constraint 1 — purely-alphanumeric paths are
// FIXED POINTS (`__cranelisp_got_primitives` is a link-time ABI literal).
#[test]
fn got_data_symbol_name_alphanumeric_paths_are_fixed_points() {
    for path in ["primitives", "prelude", "user", "macros", "sudoku9"] {
        assert_eq!(
            got_data_symbol_name(&ModuleFullPath::from(path)),
            format!("__cranelisp_got_{path}")
        );
    }
}

// spec: design/arch/fixmes/0748 constraint 3 — the `_entry` sentinel is outside
// the escape image (no path can mint it).
#[test]
fn got_data_symbol_name_entry_sentinel_outside_image() {
    assert_eq!(
        got_data_symbol_name(&ModuleFullPath::from("")),
        "__cranelisp_got__entry"
    );
    // `_entry` decodes as an illegal `_e` pair — not in the image.
    assert_eq!(decode_got_flat("_entry"), None);
    // Nearby paths that COULD be confused all mint something else.
    for path in ["entry", "_entry", ".entry", "-entry"] {
        assert_ne!(got_flat(path), "_entry", "path {path:?} must not collide with the sentinel");
    }
}

// spec: design/arch/fixmes/0748 — round-trip battery: encode→decode is the
// identity over a corpus spanning every escape class, so the mint is injective
// on everything the decoder covers.
#[test]
fn got_data_symbol_name_round_trips() {
    for path in [
        "user",
        "a.b",
        "a_b",
        "a-b",
        "a.b.c",
        "a_b.c",
        "a.b_c",
        "my-lib.sub_mod.deep",
        "compare.ord",
        "fn.option.test",
        "__x",
        "x__",
        "ümlaut.mod",
    ] {
        assert_eq!(
            decode_got_flat(&got_flat(path)).as_deref(),
            Some(path),
            "escape must round-trip for {path:?}"
        );
    }
    // Pairwise distinctness over the historically-colliding cluster.
    let cluster = ["a.b", "a_b", "a-b", "a.b.c", "a_b.c", "a.b_c"];
    for (i, p) in cluster.iter().enumerate() {
        for q in &cluster[i + 1..] {
            assert_ne!(got_flat(p), got_flat(q), "{p:?} vs {q:?}");
        }
    }
}

// ---- trait_impl_key + enrol_written_trait_impl (S119, FIXME 0869 carrier;
// design/arch/trait-impl-cache-carrier.md §4) ----

fn wt_record(methods: &[&str]) -> WrittenTraitImpl {
    WrittenTraitImpl::new(
        FQTraitName::new(ModuleFullPath::from("core"), TraitName::from("Display")),
        FQTypeName::new(ModuleFullPath::from("user"), TypeName::from("Point")),
        ModuleFullPath::from("user"),
        methods.iter().map(|m| Symbol::from(*m)).collect(),
        Visibility::Public,
    )
}

// spec: design/arch/trait-impl-cache-carrier.md §4 — the ONE key mint matches
// the (to-be-re-pointed) hand-rolled `format!("impl${}${}", type, trait)` sites
// byte-for-byte.
#[test]
fn trait_impl_key_matches_the_handrolled_grammar() {
    let r = wt_record(&["show"]);
    let key = crate::trait_impl_key(&r.impl_type, &r.trait_name);
    assert_eq!(
        key.as_ref(),
        format!("impl${}${}", r.impl_type, r.trait_name).as_str()
    );
}

// spec: design/arch/trait-impl-cache-carrier.md §4 — absent ⇒ insert the shell
// (Enrolled); identical replay ⇒ AlreadyEnrolled (idempotence carried by the
// helper, not caller bookkeeping).
#[test]
fn enrol_written_trait_impl_inserts_then_idempotent() {
    let mut home = SymbolTable::new(ModuleFullPath::from("core"));
    let r = wt_record(&["show"]);
    assert_eq!(
        enrol_written_trait_impl(&mut home, &r).expect("fresh enrol"),
        EnrolOutcome::Enrolled
    );
    let key = crate::trait_impl_key(&r.impl_type, &r.trait_name);
    match home.get(key.as_ref()) {
        Some(ModuleEntry::TraitImpl {
            trait_name,
            impl_module,
            methods,
            ..
        }) => {
            assert_eq!(trait_name, &r.trait_name);
            assert_eq!(impl_module, &r.impl_module);
            assert_eq!(methods, &r.methods);
        }
        other => panic!("expected the discovery shell, got {other:?}"),
    }
    assert_eq!(
        enrol_written_trait_impl(&mut home, &r).expect("replay"),
        EnrolOutcome::AlreadyEnrolled
    );
}

// spec: design/arch/trait-impl-cache-carrier.md §4 — divergent payload is a
// hard error naming both, never a silent pick; a non-TraitImpl occupant is
// equally divergent.
#[test]
fn enrol_written_trait_impl_rejects_divergence() {
    let mut home = SymbolTable::new(ModuleFullPath::from("core"));
    let r = wt_record(&["show"]);
    enrol_written_trait_impl(&mut home, &r).expect("fresh enrol");
    let divergent = wt_record(&["show", "extra"]);
    let err = enrol_written_trait_impl(&mut home, &divergent)
        .expect_err("divergent methods must hard-error");
    assert!(matches!(err, crate::CranelispError::ModuleError { .. }));

    // Non-TraitImpl occupant at the key.
    let mut home2 = SymbolTable::new(ModuleFullPath::from("core"));
    let key = crate::trait_impl_key(&r.impl_type, &r.trait_name);
    home2.insert(key, ModuleEntry::Ambiguous { visibility: Visibility::Public });
    let err2 = enrol_written_trait_impl(&mut home2, &r)
        .expect_err("non-TraitImpl occupant must hard-error");
    assert!(matches!(err2, crate::CranelispError::ModuleError { .. }));
}

// spec: design/arch/trait-impl-cache-carrier.md §5 (R6) — a malformed record
// (empty method list) is rejected before enrolment; nothing is inserted.
#[test]
fn enrol_written_trait_impl_rejects_malformed_record() {
    let mut home = SymbolTable::new(ModuleFullPath::from("core"));
    let r = wt_record(&[]);
    let err = enrol_written_trait_impl(&mut home, &r).expect_err("empty methods must reject");
    assert!(matches!(err, crate::CranelispError::ModuleError { .. }));
    let key = crate::trait_impl_key(&r.impl_type, &r.trait_name);
    assert!(home.get(key.as_ref()).is_none(), "nothing enrolled on rejection");
}

// spec: design/arch/trait-impl-cache-carrier.md §2 — the carrier is
// serde-visible with NO default: a sidecar missing `written_trait_impls` is a
// hard serde error (absence unrepresentable post-bump), and a populated field
// round-trips in order.
#[test]
fn written_trait_impls_serde_required_and_round_trips() {
    let mut st = SymbolTable::new(ModuleFullPath::from("user"));
    st.written_trait_impls.push(wt_record(&["show"]));
    let json = serde_json::to_string(&st).expect("serialize");
    assert!(json.contains("written_trait_impls"));
    let rt: SymbolTable = serde_json::from_str(&json).expect("round trip");
    assert_eq!(rt.written_trait_impls, st.written_trait_impls);

    // Field stripped ⇒ hard error, not a silently-empty default.
    let v: serde_json::Value = serde_json::from_str(&json).expect("value");
    let mut obj = v;
    obj.as_object_mut()
        .expect("object")
        .remove("written_trait_impls")
        .expect("field present");
    let stripped = serde_json::to_string(&obj).expect("re-serialize");
    assert!(
        serde_json::from_str::<SymbolTable>(&stripped).is_err(),
        "a pre-24 sidecar (no carrier field) must be a hard serde error"
    );
}

// spec: design/arch/platform-interface.md §1 — the platform GOT symbol is the
// DLL's ratified export_name literal; the host mint reproduces it verbatim
// (the S119 escape carves out the synthetic platform.* namespace).
#[test]
fn got_data_symbol_name_platform_carve_out_matches_the_dll_abi_literal() {
    assert_eq!(
        got_data_symbol_name(&ModuleFullPath::from("platform.stdio")),
        "__cranelisp_got_platform_stdio"
    );
    assert_eq!(
        got_data_symbol_name(&ModuleFullPath::from("platform.test-capture")),
        "__cranelisp_got_platform_test-capture",
        "the platform name joins VERBATIM (hyphen preserved) — the DLL \
         concat! literal is the authority"
    );
    // Outside the carve-out, a root module spelled `platform_stdio` escapes
    // its underscore and therefore cannot collide with a platform slab.
    assert_ne!(
        got_data_symbol_name(&ModuleFullPath::from("platform_stdio")),
        got_data_symbol_name(&ModuleFullPath::from("platform.stdio")),
    );
}
