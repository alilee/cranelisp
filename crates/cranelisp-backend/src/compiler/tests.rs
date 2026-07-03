// FnCompiler is tested via the public compile_and_run_expr API in lib.rs
// and through the Jit::compile_defn path. Direct unit testing of FnCompiler
// requires constructing a full Cranelift context, which is covered by
// the integration tests.

use super::*;
use dashmap::DashMap;
use cranelisp_types::{
    DefKind, ModuleAliasEntry, ModuleAliases, ModuleEntry, ModuleFullPath, PrimitiveBody, Scheme,
    Symbol, SymbolTable, Type, UserFnState, Visibility,
};

fn def_with_slot(slot: usize) -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::UserFn {
            fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None },
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    }
}

// ── inner-fn name discriminator (FIXME 0347 defect 1) ────────────────────

// spec: design/arch/fixmes/0347 — span-derived inner-fn names
//   (`__lambda_…`, `__wrap_…`) MUST be uniquified per monomorphic instance
//   of the enclosing fn, else N mono copies collide on one symbol.
#[test]
fn inner_fn_discriminator_uniquifies_per_mono_instance() {
    use cranelisp_types::Symbol;
    // Two monomorphic instances of one source fn carry distinct mangled
    // names; the discriminator must differ so a shared lambda span yields
    // distinct symbols.
    let a = inner_fn_discriminator_for(Some(&Symbol::from("reduce$Int+Vec")));
    let b = inner_fn_discriminator_for(Some(&Symbol::from("reduce$Float+Vec")));
    assert_ne!(a, b, "distinct mono instances must yield distinct discriminators");

    // The composed lambda names (the actual collision surface) differ.
    let span = (305usize, 312usize);
    let name_a = format!("__lambda_{a}{}_{}__", span.0, span.1);
    let name_b = format!("__lambda_{b}{}_{}__", span.0, span.1);
    assert_ne!(
        name_a, name_b,
        "two mono copies of one lambda span must emit distinct symbols \
         (else the 2nd define_function collides)"
    );

    // Sanitization: $/+/./ become _, leaving a clean Cranelift symbol.
    assert!(
        a.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'),
        "discriminator must be a clean symbol: {a:?}"
    );
    assert_eq!(a, "reduce_Int_Vec__");

    // No enclosing fn (top-level expr / nested-lambda inner compiler): empty
    // prefix — the span alone disambiguates within that scope.
    assert_eq!(inner_fn_discriminator_for(None), "");
}

// spec: design/arch/fixmes/0350 — the span-derived closure DROP-GLUE name
//   (`runtime/closure_drop_glue_<start>_<end>`) MUST be uniquified per
//   monomorphic instance the SAME way the lambda body name is (0347), else
//   N mono copies of one lambda span emit N drop-glue defs with the
//   identical name → linker `Duplicate definition of identifier`.
#[test]
fn closure_drop_glue_name_uniquifies_per_mono_instance() {
    use cranelisp_types::Symbol;
    // Two monomorphic instances of one source fn — the same shape that
    // collided on the lambda body name in 0347.
    let a = inner_fn_discriminator_for(Some(&Symbol::from("apply$Int+Vec")));
    let b = inner_fn_discriminator_for(Some(&Symbol::from("apply$Float+Vec")));

    // The composed drop-glue names (the 0350 collision surface) differ.
    let span = (2004usize, 2022usize);
    let glue_a =
        format!("runtime/closure_drop_glue_{a}{}_{}", span.0, span.1);
    let glue_b =
        format!("runtime/closure_drop_glue_{b}{}_{}", span.0, span.1);
    assert_ne!(
        glue_a, glue_b,
        "two mono copies of one lambda span must emit distinct drop-glue \
         symbols (else the 2nd define_function collides)"
    );

    // The drop-glue name MUST share the lambda body's discriminator scheme
    // so the (body, drop-glue) pair stay paired per mono instance.
    let body_a = format!("__lambda_{a}{}_{}__", span.0, span.1);
    let body_b = format!("__lambda_{b}{}_{}__", span.0, span.1);
    assert!(
        glue_a.contains(&a) && body_a.contains(&a),
        "body+drop-glue of instance A must carry the same discriminator"
    );
    assert!(
        glue_b.contains(&b) && body_b.contains(&b),
        "body+drop-glue of instance B must carry the same discriminator"
    );

    // No enclosing fn: empty prefix, span alone disambiguates — the
    // pre-0350 behaviour for top-level / nested-lambda scopes is preserved.
    let none = inner_fn_discriminator_for(None);
    assert_eq!(none, "");
    assert_eq!(
        format!("runtime/closure_drop_glue_{none}{}_{}", span.0, span.1),
        "runtime/closure_drop_glue_2004_2022"
    );
}

/// A `DefKind::PrimitiveExtern` entry — host-promised, slot-less, no
/// codegen body. Mirrors the `discover-tests` shape int seeds into the
/// `primitives` table.
fn primitive_extern_def() -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::PrimitiveExtern),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    }
}

/// An inline-dispatched primitive Def (`PrimitiveBody::Inline`) — the vec-query
/// family post FIXME-0476: no GOT slot by construction.
fn inline_primitive_def() -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::Primitive {
            body: PrimitiveBody::Inline,
            mode_summary: None,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    }
}

/// A slot-dispatched (`Extern`) primitive Def — e.g. `vec-len` post FIXME-0476.
fn extern_primitive_def(slot: usize) -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::Primitive {
            body: PrimitiveBody::Extern { got_slot: slot, borrowed_sibling_slot: None },
            mode_summary: None,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    }
}

// spec: design/backend/ownership-codegen.md §13.2 (B1-be) + FIXME 0476 —
//   `resolve_vec_query_primitive` re-keys off `PrimitiveBody::Inline`, and its
//   resolution stop condition is `is_callable_target()` (covers the slot-less
//   inline arm), NOT the S101 name-list + `callable_got_slot().is_some()` stop.
//   An inline vec primitive resolves to its canonical bare name (→ inline-emit);
//   a slot-carrying `Extern` primitive (vec-len) and a user-fn shadow resolve to
//   `None` (→ GOT-indirect dispatch), preserving shadowing precedence.
#[test]
fn resolve_vec_query_primitive_keys_on_inline_kind() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let prims = ModuleFullPath::from("primitives");
    {
        let mut st = SymbolTable::new(prims.clone());
        // The vec trio: inline-dispatched, no slot.
        st.insert(Symbol::from("vec-get"), inline_primitive_def());
        st.insert(Symbol::from("vec-set"), inline_primitive_def());
        st.insert(Symbol::from("vec-push"), inline_primitive_def());
        // vec-len: slot-dispatched Extern — NOT matched (dispatches via slot).
        st.insert(Symbol::from("vec-len"), extern_primitive_def(3));
        tables.insert(prims.clone(), st);
    }
    let user = ModuleFullPath::from("user");
    tables.insert(user.clone(), SymbolTable::new(user.clone()));
    let aliases: ModuleAliases = DashMap::new();

    // Each inline vec op resolves to its canonical bare name (→ inline emit).
    for name in ["vec-get", "vec-set", "vec-push"] {
        assert_eq!(
            resolve_vec_query_primitive(&tables, &aliases, &user, &Symbol::from(name)),
            Some(Symbol::from(name)),
            "inline primitive {name} must resolve to its canonical name via is_callable_target()",
        );
    }
    // vec-len is Extern (slot-carrying) → NOT an inline vec-query target.
    assert_eq!(
        resolve_vec_query_primitive(&tables, &aliases, &user, &Symbol::from("vec-len")),
        None,
        "vec-len dispatches through its slot — never inline-emitted as a value",
    );
    // Absent name → None.
    assert_eq!(
        resolve_vec_query_primitive(&tables, &aliases, &user, &Symbol::from("nonesuch")),
        None,
    );
}

// spec: design/backend/ownership-codegen.md §13.2 (B1-be) + FIXME 0476 — a
//   user-defined fn shadowing a vec-op name resolves FIRST (a callable target
//   with a slot) and reports `None` here, so it keeps ordinary GOT-indirect
//   dispatch. Precedence is unchanged by the slot-presence → is_callable_target
//   stop-predicate flip.
#[test]
fn resolve_vec_query_primitive_user_shadow_keeps_got_dispatch() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let user = ModuleFullPath::from("user");
    {
        let mut st = SymbolTable::new(user.clone());
        // A user fn named `vec-get` shadows the primitive in the current module.
        st.insert(Symbol::from("vec-get"), def_with_slot(9));
        tables.insert(user.clone(), st);
    }
    let prims = ModuleFullPath::from("primitives");
    {
        let mut st = SymbolTable::new(prims.clone());
        st.insert(Symbol::from("vec-get"), inline_primitive_def());
        tables.insert(prims.clone(), st);
    }
    let aliases: ModuleAliases = DashMap::new();

    // Current-module (user) shadow resolves first: a slot-carrying UserFn →
    // `None` → GOT-indirect dispatch (not inline-emitted).
    assert_eq!(
        resolve_vec_query_primitive(&tables, &aliases, &user, &Symbol::from("vec-get")),
        None,
        "a user-fn shadow keeps GOT-indirect dispatch (precedence unchanged)",
    );
}

// spec: design/arch/test-discovery.md §6 "Backend — one kind-dispatched
//       call arm"; BC §3 invariant 8 / §7 types — a `DefKind::PrimitiveExtern`
//       callee (`discover-tests`) carries `got_slot: None`, so
//       `resolve_got_target` misses it; `resolve_extern_target` recognises
//       the kind and returns its ABI key (the symbol-table key, no
//       jit_name) for a `Linkage::Import` lowering. Confirms global-fallback
//       resolution (the call site has no explicit import of `primitives`)
//       and that a non-extern Def is NOT matched.
#[test]
fn resolve_extern_target_finds_primitive_extern_by_kind() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();

    // Synthetic `primitives` module seeds `discover-tests` as a
    // PrimitiveExtern (got_slot: None) and an ordinary slotted Def.
    let prims = ModuleFullPath::from("primitives");
    {
        let mut st = SymbolTable::new(prims.clone());
        st.insert(Symbol::from("discover-tests"), primitive_extern_def());
        st.insert(Symbol::from("add-i64"), def_with_slot(7));
        tables.insert(prims.clone(), st);
    }
    // Call site is in `user`, with no import of `primitives`.
    let user = ModuleFullPath::from("user");
    tables.insert(user.clone(), SymbolTable::new(user.clone()));
    let aliases: ModuleAliases = DashMap::new();

    // The extern resolves via global fallback to its ABI key.
    assert_eq!(
        resolve_extern_target(&tables, &aliases, &user, &Symbol::from("discover-tests")),
        Some("discover-tests".to_string()),
        "PrimitiveExtern callee resolves to its symbol-table key (ABI name)",
    );
    // `resolve_got_target` does NOT match it (no GOT slot).
    assert_eq!(
        resolve_got_target(&tables, &aliases, &user, &Symbol::from("discover-tests")),
        None,
        "a PrimitiveExtern has no GOT slot — the GOT path must miss it",
    );
    // A slotted ordinary Def is NOT a PrimitiveExtern.
    assert_eq!(
        resolve_extern_target(&tables, &aliases, &user, &Symbol::from("add-i64")),
        None,
        "a slotted UserFn/primitive is not a PrimitiveExtern",
    );
    // Absent name resolves to nothing.
    assert_eq!(
        resolve_extern_target(&tables, &aliases, &user, &Symbol::from("nonesuch")),
        None,
    );
}

/// A `DefKind::PlatformEffect` Def. Post the S83 Option-A reshape (FIXME
/// 0358) a platform effect ALWAYS carries its GOT slot on the variant — it
/// is a GOT-addressable callable, so there is no longer a slot-less
/// "as-built" PlatformEffect shape to contrast against.
fn platform_effect_def_new_shape(slot: usize) -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::PlatformEffect {
            scheduling_class: cranelisp_types::SchedulingClass::Sequential,
            poll_shape: false,
            got_slot: slot,
            mode_summary: None,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    }
}

// spec: design/arch/platform-interface.md §6.2/§6.3; BC §3 "the
//       platform-interface codegen role" — the platform GOT-indirect call
//       arm activates for a `DefKind::PlatformEffect` entry, which (post the
//       S83 Option-A reshape, FIXME 0358) ALWAYS carries its GOT slot on the
//       variant: `resolve_got_target` resolves it to (module, slot) so the
//       dispatch arm emits GOT-indirect. A genuinely slot-less kind
//       (`PrimitiveExtern`) misses the GOT path and falls to the
//       direct-extern (`Linkage::Import`) path.
#[test]
fn platform_effect_new_shape_resolves_got_indirect() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let plat = ModuleFullPath::from("platform.shapes");
    {
        let mut st = SymbolTable::new(plat.clone());
        // PlatformEffect: carries its got_slot on the variant (DLL-exported
        // GOT adoption) → GOT-indirect resolvable.
        st.insert(Symbol::from("rectangle-area"), platform_effect_def_new_shape(2));
        // A genuinely slot-less host-promised extern — misses the GOT path
        // and stays on the direct-extern fallback.
        st.insert(Symbol::from("print"), primitive_extern_def());
        tables.insert(plat.clone(), st);
    }
    let user = ModuleFullPath::from("user");
    tables.insert(user.clone(), SymbolTable::new(user.clone()));
    let aliases: ModuleAliases = DashMap::new();

    // PlatformEffect resolves to (defining module, slot) → GOT-indirect arm.
    assert_eq!(
        resolve_got_target(&tables, &aliases, &user, &Symbol::from("rectangle-area")),
        Some((plat.clone(), 2)),
        "PlatformEffect resolves GOT-indirect at its adopted slot",
    );
    // The slot-less PrimitiveExtern misses the GOT path → direct-extern stays live.
    assert_eq!(
        resolve_got_target(&tables, &aliases, &user, &Symbol::from("print")),
        None,
        "a slot-less PrimitiveExtern stays on the direct-extern path",
    );
}

// spec: design/arch/bounded-contexts.md §5 invariant 9 + §3 "the
//       platform-dispatch fn-name bake" (S81 / FIXME 0327, the dispatch
//       funnel step 2/4) — `resolve_platform_effect_target` is the
//       discriminator that decides whether the GOT-indirect arm stamps the
//       baked fn-name into the returned Effect node's field-3. It must
//       return `Some((defining_module, slot, defining_bare_name))` for a
//       new-shape `DefKind::PlatformEffect`, follow Import edges to the
//       DEFINING entry (so the baked FQ name is canonical, not the local
//       alias), and return `None` for every other kind — so ONLY the
//       PlatformEffect arm stamps and user fns / primitives / trait methods
//       are left untouched.
#[test]
fn resolve_platform_effect_target_discriminates_kind_and_follows_imports() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let plat = ModuleFullPath::from("platform.shapes");
    {
        let mut st = SymbolTable::new(plat.clone());
        // New-shape PlatformEffect — the only kind that stamps.
        st.insert(Symbol::from("rectangle-area"), platform_effect_def_new_shape(2));
        // A slotted USER fn at the same module — must NOT match.
        st.insert(Symbol::from("helper"), def_with_slot(5));
        tables.insert(plat.clone(), st);
    }
    // `user` imports `rectangle-area` under a local alias `area`.
    let user = ModuleFullPath::from("user");
    {
        let mut st = SymbolTable::new(user.clone());
        st.insert(
            Symbol::from("area"),
            ModuleEntry::Import {
                source: cranelisp_types::FQSymbol {
                    module: plat.clone(),
                    symbol: Symbol::from("rectangle-area"),
                },
                visibility: Visibility::Public,
            },
        );
        tables.insert(user.clone(), st);
    }
    let aliases: ModuleAliases = DashMap::new();

    // Direct reference in the defining module: Some(module, slot, bare).
    assert_eq!(
        resolve_platform_effect_target(
            &tables, &aliases, &plat, &Symbol::from("rectangle-area")
        ),
        Some((plat.clone(), 2, Symbol::from("rectangle-area"))),
        "new-shape PlatformEffect resolves to (defining module, slot, defining bare name)",
    );
    // Import-aliased reference resolves to the DEFINING entry — so the baked
    // FQ name is `platform.shapes/rectangle-area`, never `user/area`.
    assert_eq!(
        resolve_platform_effect_target(&tables, &aliases, &user, &Symbol::from("area")),
        Some((plat.clone(), 2, Symbol::from("rectangle-area"))),
        "Import edge resolves to the defining module + canonical name, not the local alias",
    );
    // A slotted USER fn is NOT a PlatformEffect → None (its arm must not stamp).
    assert_eq!(
        resolve_platform_effect_target(&tables, &aliases, &plat, &Symbol::from("helper")),
        None,
        "a slotted UserFn must not be discriminated as a platform effect",
    );
    // Absent name → None.
    assert_eq!(
        resolve_platform_effect_target(&tables, &aliases, &user, &Symbol::from("nonesuch")),
        None,
    );
}

/// A poll-shape `DefKind::PlatformEffect` (`poll_shape: true`, `blocking == 0`)
/// with a one-param `Fn` scheme, so `resolve_poll_effect_target` can lift its
/// param types for the state-closure drop glue (FIXME 0457, S94 R1).
fn poll_effect_def(slot: usize) -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: std::collections::HashMap::new(),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![Symbol::from("n")],
        kind: Box::new(DefKind::PlatformEffect {
            scheduling_class: cranelisp_types::SchedulingClass::Commutative,
            poll_shape: true,
            got_slot: slot,
            mode_summary: None,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    }
}

// spec: design/arch/effect-concurrency.md §"The ratified backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)" (a)
// + design/backend/io-trampoline.md §12.6 — `resolve_poll_effect_target` is the
// keying discriminator for the backend's poll-construction arm: it returns
// `Some((module, slot, param_types))` ONLY for a `poll_shape: true`
// PlatformEffect (so that effect builds an `IO_TAG_EFFECT_POLL` node), and
// `None` for a `poll_shape: false` blocking effect (so it takes the unchanged
// GOT-indirect call path — the default build constructs no poll node,
// byte-identical-off). No cargo feature: the arm is data-keyed (Principle 11).
#[test]
fn resolve_poll_effect_target_keys_on_poll_shape() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let plat = ModuleFullPath::from("platform.async-demo");
    {
        let mut st = SymbolTable::new(plat.clone());
        // poll-shape (blocking==0) → keys the poll-construction arm.
        st.insert(Symbol::from("async-read"), poll_effect_def(3));
        // blocking (poll_shape:false, every v6 platform) → must NOT key it.
        st.insert(Symbol::from("print"), platform_effect_def_new_shape(2));
        tables.insert(plat.clone(), st);
    }
    let aliases: ModuleAliases = DashMap::new();

    // poll-shape resolves to (defining module, slot, param types) — the keying.
    let got = resolve_poll_effect_target(&tables, &aliases, &plat, &Symbol::from("async-read"));
    assert!(
        matches!(&got, Some((m, 3, params, _class)) if m == &plat && params.len() == 1),
        "poll-shape effect must key the poll arm with its param types, got {got:?}",
    );
    // blocking effect → None (unchanged call path; byte-identical-off).
    assert_eq!(
        resolve_poll_effect_target(&tables, &aliases, &plat, &Symbol::from("print")),
        None,
        "a blocking (poll_shape:false) effect must NOT key the poll-construction arm",
    );
}

// spec: design/arch/test-discovery.md §6 — `resolve_extern_target` follows
//       an Import edge to the defining module and returns the DEFINING
//       entry's key (the canonical ABI name), not the importing alias.
#[test]
fn resolve_extern_target_follows_import_edge() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let prims = ModuleFullPath::from("primitives");
    {
        let mut st = SymbolTable::new(prims.clone());
        st.insert(Symbol::from("discover-tests"), primitive_extern_def());
        tables.insert(prims.clone(), st);
    }
    // `user` imports `discover-tests` under a local alias `discover`.
    let user = ModuleFullPath::from("user");
    {
        let mut st = SymbolTable::new(user.clone());
        st.insert(
            Symbol::from("discover"),
            ModuleEntry::Import {
                source: cranelisp_types::FQSymbol {
                    module: prims.clone(),
                    symbol: Symbol::from("discover-tests"),
                },
                visibility: Visibility::Public,
            },
        );
        tables.insert(user.clone(), st);
    }
    let aliases: ModuleAliases = DashMap::new();
    assert_eq!(
        resolve_extern_target(&tables, &aliases, &user, &Symbol::from("discover")),
        Some("discover-tests".to_string()),
        "Import edge resolves to the defining module's ABI key, not the local alias",
    );
}

// spec: spec/08-modules.md §8.6.6 step 5 — qualified-name resolution
//       substitutes a module-alias prefix with its target before walking
//       the symbol tables. S75 W2 (D41 rotation) threaded `module_aliases`
//       into `resolve_got_target` to perform this substitution; without it
//       a qualified `alias/name` whose prefix is an alias (not a real
//       child/absolute module) would not resolve.
#[test]
fn resolve_got_target_follows_module_alias_prefix() {
    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    // Real target module `core.string` defines `concat` at GOT slot 3.
    let target = ModuleFullPath::from("core.string");
    {
        let mut st = SymbolTable::new(target.clone());
        st.insert(Symbol::from("concat"), def_with_slot(3));
        tables.insert(target.clone(), st);
    }
    // Current module `user` has NO `str` child module and NO `concat`.
    let current = ModuleFullPath::from("user");
    tables.insert(current.clone(), SymbolTable::new(current.clone()));

    // Alias `user.str` → `core.string` (an import-alias owned by `user`).
    let aliases: ModuleAliases = DashMap::new();
    aliases.insert(
        ModuleFullPath::from("user.str"),
        ModuleAliasEntry::new(target.clone(), Visibility::Private, cranelisp_types::Span::SYNTHETIC),
    );

    // With the alias table, `str/concat` from `user` resolves to
    // (core.string, slot 3) via §8.6.6 step-5 substitution.
    let resolved = resolve_got_target(
        &tables,
        &aliases,
        &current,
        &Symbol::from("str/concat"),
    );
    assert_eq!(
        resolved,
        Some((target.clone(), 3)),
        "alias prefix `str` must substitute to `core.string` and resolve `concat`"
    );

    // Without the alias entry, the same qualified name does NOT resolve
    // (no `user.str` child module, no absolute `str` module).
    let empty_aliases: ModuleAliases = DashMap::new();
    let unresolved = resolve_got_target(
        &tables,
        &empty_aliases,
        &current,
        &Symbol::from("str/concat"),
    );
    assert_eq!(
        unresolved, None,
        "without the alias, `str/concat` has no child/absolute target to resolve"
    );
}
