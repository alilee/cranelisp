//! Per-submodule test module for `monomorphise.rs` — the monomorphisation
//! engine (`monomorphise_call`, `instantiate_constrained`,
//! `recheck_body_for_mono`) + the mangling primitives (`build_mangled_name`,
//! `concrete_type_name`). Relocated verbatim from the pooled `traits/tests.rs`
//! (S102 FIXME 0497 de-pool) and EXTENDED with the instantiation-matrix
//! gap-fill (0497 step ii: value-fact-asserting cells at the mint seam — the
//! crate-side pins for the 0488 defect class), per METHOD §2.2 / Principle 23.

use cranelisp_types::{
    DefKind, Defn, DefnVariant, Expr, ModuleEntry, ModuleFullPath, Span, Symbol, TopLevel,
    Type, TypeName, UserFnState, Visibility,
};

use crate::checker::TypeCheckEnv;
use super::*;
use crate::traits::test_helpers::*;

// -----------------------------------------------------------------------
// concrete_type_name — the bare-TypeName extractor used by the mangler.
// -----------------------------------------------------------------------

// spec: 07-traits §7.4.1 — concrete_type_name maps Int to TypeName
#[test]
fn test_concrete_type_name_int() {
    assert_eq!(concrete_type_name(&Type::Int), Some(TypeName::from("Int")));
}

// spec: 07-traits §7.4.1 — concrete_type_name maps Float to TypeName
#[test]
fn test_concrete_type_name_float() {
    assert_eq!(
        concrete_type_name(&Type::Float),
        Some(TypeName::from("Float"))
    );
}

// spec: 07-traits §7.4.1 — concrete_type_name maps Bool to TypeName
#[test]
fn test_concrete_type_name_bool() {
    assert_eq!(
        concrete_type_name(&Type::Bool),
        Some(TypeName::from("Bool"))
    );
}

// spec: 07-traits §7.4.1 — concrete_type_name maps String to TypeName
#[test]
fn test_concrete_type_name_string() {
    assert_eq!(
        concrete_type_name(&Type::String),
        Some(TypeName::from("String"))
    );
}

// spec: 07-traits §7.4.1 — concrete_type_name maps ADT to its TypeName
#[test]
fn test_concrete_type_name_adt() {
    assert_eq!(
        concrete_type_name(&Type::ADT(test_fqtn("Color"), vec![])),
        Some(TypeName::from("Color"))
    );
}

// spec: 07-traits §7.4.1 — type variable has no concrete type name
#[test]
fn test_concrete_type_name_var_is_none() {
    assert_eq!(concrete_type_name(&Type::Var(0)), None);
}

// spec: 07-traits §7.4.1 — a `Fn` type is concrete but has no single bare
// TypeName (`concrete_type_name` returns `None`). `concrete_type_name` is
// retained for trait-impl TARGET naming (impl-on-type-constructor, head-name
// only); the mono mangler no longer routes through it (FIXME 0519 — it routes
// through the total `program::mangle_type`, which recurses `Fn` rather than
// dropping it; see the Fn-axis cell below).
#[test]
fn concrete_type_name_fn_is_none() {
    let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
    assert!(fn_ty.is_concrete(), "a Fn over concrete arg/ret is itself concrete");
    assert_eq!(concrete_type_name(&fn_ty), None);
}

// =======================================================================
// build_mangled_name — THE canonical home-qualified lossless mono mangler
// (FIXME 0519). Grammar: `{home}/{bare}${recursive-concrete-sig}`. The
// strategy-derived matrix below (METHOD §2.2, seam × class) asserts the
// SPECIFIC produced key on every distinguishing axis — ADT-arg, home, Fn-arg,
// nesting, arg-order — plus idempotency/dedup, mirror consistency, and the
// scalar regression. Each cell asserts a string, not "no panic".
// =======================================================================

// A stable home for the pure-mangler cells.
fn m() -> ModuleFullPath {
    ModuleFullPath::from("m")
}

// --- Scalar regression (class: complexity — the common path stays sane) ---

// spec: design/typecheck/monomorphisation.md §3.5 — two scalar args join with
// `+`, home-qualified prefix `{home}/`.
#[test]
fn build_mangled_name_two_int_args() {
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("add"), &[Type::Int, Type::Int]),
        "m/add$Int+Int"
    );
}

// spec: design/typecheck/monomorphisation.md §3.5 — a distinct scalar set
// yields a distinct key (the collision-freedom property the mint seam needs).
#[test]
fn build_mangled_name_two_float_args_distinct_from_int() {
    let int_key = build_mangled_name(&m(), &Symbol::from("add"), &[Type::Int, Type::Int]);
    let float_key = build_mangled_name(&m(), &Symbol::from("add"), &[Type::Float, Type::Float]);
    assert_eq!(float_key, "m/add$Float+Float");
    assert_ne!(int_key, float_key);
}

// spec: design/typecheck/monomorphisation.md §3.5 — edge: single-arg mangle has
// no `+` separator.
#[test]
fn build_mangled_name_single_arg_no_separator() {
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("id"), &[Type::Int]),
        "m/id$Int"
    );
}

// --- ADT-arg axis (0483: erasing ADT args collapsed distinct bodies) ---

// spec: design/typecheck/monomorphisation.md §3.5 — a nullary ADT param mangles
// to its FQTypeName (`{type-home}/{name}`, the canonical `mangle_type` form the
// multi-sig mangler already used — unified here, Principle 7). `test_fqtn`
// homes the type in module `test`.
#[test]
fn build_mangled_name_adt_nullary() {
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("f"), &[Type::ADT(test_fqtn("Color"), vec![])]),
        "m/f$test/Color"
    );
}

// spec: design/typecheck/monomorphisation.md §3.5 — CURE 0483: `Vec Int` and
// `Vec String` mint DISTINCT keys (the ADT arg is recursed, not erased). On
// HEAD both collapsed to `f$Vec`.
#[test]
fn build_mangled_name_adt_arg_distinguishes_element_type() {
    let vec_int = Type::ADT(test_fqtn("Vec"), vec![Type::Int]);
    let vec_str = Type::ADT(test_fqtn("Vec"), vec![Type::String]);
    let ki = build_mangled_name(&m(), &Symbol::from("f"), &[vec_int]);
    let ks = build_mangled_name(&m(), &Symbol::from("f"), &[vec_str]);
    assert_eq!(ki, "m/f$test/Vec$Int");
    assert_eq!(ks, "m/f$test/Vec$String");
    assert_ne!(ki, ks, "distinct ADT element types MUST mint distinct keys (0483)");
}

// spec: design/typecheck/monomorphisation.md §3.5 — edge: NESTED ADT args
// recurse fully — `Vec (Vec Int)` ≠ `Vec (Vec String)`.
#[test]
fn build_mangled_name_nested_adt_arg() {
    let vv_int = Type::ADT(test_fqtn("Vec"), vec![Type::ADT(test_fqtn("Vec"), vec![Type::Int])]);
    let vv_str = Type::ADT(test_fqtn("Vec"), vec![Type::ADT(test_fqtn("Vec"), vec![Type::String])]);
    assert_eq!(build_mangled_name(&m(), &Symbol::from("f"), &[vv_int]), "m/f$test/Vec$test/Vec$Int");
    assert_eq!(build_mangled_name(&m(), &Symbol::from("f"), &[vv_str]), "m/f$test/Vec$test/Vec$String");
}

// spec: design/typecheck/monomorphisation.md §3.5 — edge: a 2-arg ADT preserves
// arg ORDER — `Pair Int String` ≠ `Pair String Int`.
#[test]
fn build_mangled_name_two_arg_adt_order_matters() {
    let pair_is = Type::ADT(test_fqtn("Pair"), vec![Type::Int, Type::String]);
    let pair_si = Type::ADT(test_fqtn("Pair"), vec![Type::String, Type::Int]);
    let k1 = build_mangled_name(&m(), &Symbol::from("f"), &[pair_is]);
    let k2 = build_mangled_name(&m(), &Symbol::from("f"), &[pair_si]);
    assert_eq!(k1, "m/f$test/Pair$Int+String");
    assert_eq!(k2, "m/f$test/Pair$String+Int");
    assert_ne!(k1, k2, "ADT arg order MUST be distinguishing");
}

// --- Home axis (0508: home-blindness silently mis-dispatched) ---

// spec: design/typecheck/monomorphisation.md §3.5 — CURE 0508: the SAME bare
// name at the SAME arg type in two DIFFERENT defining modules mints DISTINCT
// keys (home-qualified). On HEAD both minted `twist$Int`.
#[test]
fn build_mangled_name_home_distinguishes_same_named_generics() {
    let ka = build_mangled_name(&ModuleFullPath::from("a"), &Symbol::from("twist"), &[Type::Int]);
    let kb = build_mangled_name(&ModuleFullPath::from("b"), &Symbol::from("twist"), &[Type::Int]);
    assert_eq!(ka, "a/twist$Int");
    assert_eq!(kb, "b/twist$Int");
    assert_ne!(ka, kb, "same name + same args + different home MUST be distinct (0508)");
}

// spec: design/typecheck/monomorphisation.md §3.5 — NEGATIVE/dedup: same
// name + same home + same args mint the IDENTICAL key (the legitimate share —
// the fix must NOT over-split the genuine same-instantiation case).
#[test]
fn build_mangled_name_same_home_same_args_dedups() {
    let k1 = build_mangled_name(&ModuleFullPath::from("a"), &Symbol::from("twist"), &[Type::Int]);
    let k2 = build_mangled_name(&ModuleFullPath::from("a"), &Symbol::from("twist"), &[Type::Int]);
    assert_eq!(k1, k2, "identical (home, name, sig) MUST mangle identically — dedup still works");
}

// --- Fn-arg axis (the latent third: filter_map dropped `Fn` params) ---

// spec: design/typecheck/monomorphisation.md §3.5 — CURE the latent Fn-drop:
// a `Fn`-typed param is RECURSED (arg+ret), not dropped. On HEAD the whole `Fn`
// param vanished (`concrete_type_name` → None → filter_map drop).
#[test]
fn build_mangled_name_recurses_fn_typed_param() {
    let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("reduce"), &[Type::Int, fn_ty]),
        "m/reduce$Int+Fn(Int;Int)"
    );
}

// spec: design/typecheck/monomorphisation.md §3.5 — CURE the latent Fn-drop:
// two instantiations distinguished ONLY by a `Fn`-typed param mint DISTINCT
// keys. On HEAD both dropped the `Fn` → both `apply$` → collision.
#[test]
fn build_mangled_name_fn_param_distinguishes_instantiations() {
    let fn_ii = Type::Fn(vec![Type::Int], Box::new(Type::Int));
    let fn_bb = Type::Fn(vec![Type::Bool], Box::new(Type::Bool));
    let k1 = build_mangled_name(&m(), &Symbol::from("apply"), &[fn_ii]);
    let k2 = build_mangled_name(&m(), &Symbol::from("apply"), &[fn_bb]);
    assert_eq!(k1, "m/apply$Fn(Int;Int)");
    assert_eq!(k2, "m/apply$Fn(Bool;Bool)");
    assert_ne!(k1, k2, "a Fn-param-only difference MUST be distinguishing (latent third axis)");
}

// spec: design/typecheck/monomorphisation.md §3.5 — edge: NESTED `Fn` (a Fn
// returning a Fn) recurses with balanced parens keeping extents unambiguous.
#[test]
fn build_mangled_name_nested_fn_param() {
    // (Fn [Int] (Fn [Int] Bool))
    let inner = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
    let outer = Type::Fn(vec![Type::Int], Box::new(inner));
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("k"), &[outer]),
        "m/k$Fn(Int;Fn(Int;Bool))"
    );
}

// --- Depth ≥3 + cross-axis nesting (recursion terminates + distinguishes at
//     depth, and the ADT axis and Fn axis compose) ---

// spec: design/typecheck/monomorphisation.md §3.5 — edge: nesting depth 3. The
// recursion terminates AND distinguishes `Vec (Vec (Vec Int))` from the String
// tail. Dev's matrix pinned depth 2 (`nested_adt_arg`); this pins depth ≥3 per
// the strategy-matrix requirement (each additional level recurses, no cap).
#[test]
fn build_mangled_name_triple_nested_adt_arg() {
    let vvv_int = Type::ADT(
        test_fqtn("Vec"),
        vec![Type::ADT(test_fqtn("Vec"), vec![Type::ADT(test_fqtn("Vec"), vec![Type::Int])])],
    );
    let vvv_str = Type::ADT(
        test_fqtn("Vec"),
        vec![Type::ADT(test_fqtn("Vec"), vec![Type::ADT(test_fqtn("Vec"), vec![Type::String])])],
    );
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("f"), &[vvv_int]),
        "m/f$test/Vec$test/Vec$test/Vec$Int"
    );
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("f"), &[vvv_str]),
        "m/f$test/Vec$test/Vec$test/Vec$String"
    );
}

// spec: design/typecheck/monomorphisation.md §3.5 — cross-axis: an ADT whose
// argument is a `Fn` recurses through BOTH axes (`Vec (Fn [Int] Int)`). Neither
// the pure-ADT cells nor the pure-Fn cells cover the ADT-contains-Fn composition
// — this pins that the two axes compose in the one canonical mangler.
#[test]
fn build_mangled_name_adt_arg_containing_fn() {
    let vec_of_fn = Type::ADT(
        test_fqtn("Vec"),
        vec![Type::Fn(vec![Type::Int], Box::new(Type::Int))],
    );
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("f"), &[vec_of_fn]),
        "m/f$test/Vec$Fn(Int;Int)"
    );
}

// spec: design/typecheck/monomorphisation.md §3.5 — cross-axis: a `Fn` whose
// RETURN type is an ADT recurses the ret position into the ADT axis
// (`Fn [Int] (Vec Int)`). Complements `nested_fn_param` (Fn-returns-Fn) and
// `adt_arg_containing_fn` (ADT-contains-Fn) — closes the 2×2 axis-composition
// matrix. The balanced `Fn(…;…)` parens keep the ADT ret extent unambiguous.
#[test]
fn build_mangled_name_fn_returning_adt() {
    let fn_ret_vec = Type::Fn(
        vec![Type::Int],
        Box::new(Type::ADT(test_fqtn("Vec"), vec![Type::Int])),
    );
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("g"), &[fn_ret_vec]),
        "m/g$Fn(Int;test/Vec$Int)"
    );
}

// spec: design/typecheck/monomorphisation.md §3.5 — a bare `String` scalar param
// mangles to `String` (the scalar cells pin Int/Float; String/Bool were only
// exercised structurally inside ADT/Fn args — this pins the bare-scalar leg).
#[test]
fn build_mangled_name_bare_string_scalar() {
    assert_eq!(
        build_mangled_name(&m(), &Symbol::from("id"), &[Type::String]),
        "m/id$String"
    );
}

// --- Mirror consistency (the 0508 dedup/name inconsistency guard) ---

// spec: design/typecheck/monomorphisation.md §3.5 — the pass4 seen-dedup key and
// the minted mono name are produced by the SAME function over the SAME inputs,
// so they are byte-identical for one instantiation. This cell pins that the
// key path (`build_mangled_name(home, fn, arg_types)`) and the name path
// (`build_mangled_name(home, fn, concrete_param_types)`) agree when arg_types ==
// concrete_param_types (the concrete-dispatch case) — the inconsistency 0508
// exploited (home-blind key vs would-be home-name).
#[test]
fn build_mangled_name_dedup_key_equals_minted_name() {
    let home = ModuleFullPath::from("a");
    let name = Symbol::from("twist");
    let args = [Type::Int, Type::Int];
    // "name path" — what monomorphise_call mints from concrete_param_types.
    let minted = build_mangled_name(&home, &name, &args);
    // "key path" — what the pass4 seen map keys on from the call-site arg_types.
    let dedup_key = build_mangled_name(&home, &name, &args);
    assert_eq!(minted, dedup_key, "dedup key and minted name MUST be one string (mirror)");
    assert_eq!(minted, "a/twist$Int+Int");
}

// spec: design/typecheck/monomorphisation.md §9.3 (Principle 18) — NEGATIVE: a
// non-concrete (`Var`) param is a lossy-name hazard. The `build_mangled_name`
// tripwire (`debug_assert`) fires rather than emitting the shared `Var` token
// that would collapse two distinct partial instantiations.
#[test]
#[should_panic(expected = "non-concrete param")]
fn build_mangled_name_tripwire_on_non_concrete_param() {
    let _ = build_mangled_name(&m(), &Symbol::from("f"), &[Type::Int, Type::Var(7)]);
}

// -----------------------------------------------------------------------
// Mono-instance minting via the check_repl_input / monomorphise_call seams.
// -----------------------------------------------------------------------

// spec: design/typecheck/ast-annotation.md §9.4 — mono specialisation ast + distinct GOT slot
#[test]
fn wave0_mono_entry_registered_with_distinct_got_slot() {
    let mut tc = tc_with_prims();
    register_num_for_int(&mut tc);

    // Template: (defn add [x y] (+ x y))
    let add_defn = cranelisp_types::TopLevel::Defn(Defn {
        name: Symbol::from("add"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), Span::new(18, 19))),
                args: vec![
                    Expr::var(Symbol::from("x"), Span::new(20, 21)),
                    Expr::var(Symbol::from("y"), Span::new(22, 23)),
                ],
                span: Span::new(17, 24),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 25),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 25),
    });
    tc.check_repl_input_self(&add_defn).unwrap();

    // Concrete call-site triggers monomorphisation: (defn main [] (add 1 2))
    let main_defn = cranelisp_types::TopLevel::Defn(Defn {
        name: Symbol::from("main"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add"), Span::new(200, 203))),
                args: vec![
                    Expr::IntLit { value: 1, span: Span::new(204, 205), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(206, 207), inferred_type: None },
                ],
                span: Span::new(199, 208),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(180, 209),
        }],
        visibility: Visibility::Public,
        span: Span::new(180, 209),
    });
    tc.check_repl_input_self(&main_defn).unwrap();

    // Template entry: kind UserFn { constrained_fn: Some(_) }.
    // NOTE: §9.2 of design/typecheck/ast-annotation.md says the template's `ast`
    // "stays None" to signal "skip at codegen". That is the future intent — the
    // filter in `defined_symbols()` (§9.5) gates on `kind`, not `ast`, so the
    // invariant that matters today is `kind`. The mono entry below carries the
    // compilable body.
    let template_got_slot = {
        let st = tc.symbol_table();
        match st.get("add") {
            Some(entry @ ModuleEntry::Def { kind, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Constrained(_) }
                    ),
                    "template 'add' kind should be UserFn(Constrained), got {:?}",
                    kind
                );
                // S83 (Principle 20): a constrained template carries no slot
                // (read via the accessor) — `None` by construction.
                entry.callable_got_slot()
            }
            other => panic!("'add' template should be Def entry, got {:?}", other),
        }
    };

    // Mono entry: kind UserFn(Concrete), ast: Some(..), has a GOT slot distinct from template.
    let mono_got_slot = {
        let st = tc.symbol_table();
        // FIXME 0519: mono names are home-qualified `{home}/{bare}$sig`; the
        // fixture's current module is `test`.
        match st.get("test/add$Int+Int") {
            Some(entry @ ModuleEntry::Def { kind, ast, .. }) => {
                assert!(
                    matches!(
                        kind.as_ref(),
                        DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                    ),
                    "mono 'test/add$Int+Int' kind should be UserFn(Concrete), got {:?}",
                    kind
                );
                let defn = ast.as_ref().expect("mono must carry ast: Some(..)");
                // Per S69 Submission 35: ast: Option<DefnVariant>; the name lives on
                // the symbol-table key ("add$Int+Int" here), not on the variant.

                // All inferred types on the mono body are concrete.
                assert_types_concrete(&defn.body);

                // The resolved_call on the + call site must be set (SigDispatch or
                // TraitMethod — both are valid concrete resolutions post-mono).
                if let Expr::Apply { resolved_call, .. } = &defn.body {
                    assert!(
                        resolved_call.is_some(),
                        "mono body's + call site must have resolved_call set"
                    );
                } else {
                    panic!("mono body should be Apply, got {:?}", defn.body);
                }

                entry.callable_got_slot().expect("mono must have a GOT slot assigned")
            }
            other => panic!("'test/add$Int+Int' mono should be Def entry, got {:?}", other),
        }
    };

    // Distinctness: template slot (if any) must differ from the mono slot.
    // Constrained templates usually get no slot (`None`); in that case any
    // Some(slot) on the mono is trivially distinct.
    if let Some(t) = template_got_slot {
        assert_ne!(
            t, mono_got_slot,
            "template and mono must have distinct GOT slots"
        );
    }
}

// spec: design/typecheck/ast-annotation.md §9.4 — resolved-stage annotations
// live on the `MonoDefn.defn` AST, not on a side map (FIXME 0033).
//
// Pins the invariant that makes the S81 W-G `MonoDefn` side-map drop safe:
// `monomorphise_call` returns a `MonoDefn` whose `defn` AST already carries
// every `inferred_type` (concrete) and every call-site `resolved_call`. The
// dropped `MonoDefn.resolutions` / `MonoDefn.expr_types` Span-keyed maps held
// exactly this data; with them gone, the single source of truth is the AST.
// This test reads the returned `MonoDefn` directly (not the registered
// symbol-table entry) so it asserts the contract on `MonoDefn` itself.
#[test]
fn fixme0033_monodefn_annotations_live_on_defn_ast_not_side_maps() {
    let mut tc = tc_with_prims();
    register_num_for_int(&mut tc);

    // Template: (defn add [x y] (+ x y)) — constrained on Num via the `+`.
    let add_defn = cranelisp_types::TopLevel::Defn(Defn {
        name: Symbol::from("add"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), Span::new(18, 19))),
                args: vec![
                    Expr::var(Symbol::from("x"), Span::new(20, 21)),
                    Expr::var(Symbol::from("y"), Span::new(22, 23)),
                ],
                span: Span::new(17, 24),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 25),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 25),
    });
    tc.check_repl_input_self(&add_defn).unwrap();

    // Drive `monomorphise_call` directly for `(add 1 2)` and capture the
    // returned `MonoDefn`. Construct the env borrowing individual fields so
    // `&mut tc.state` stays available (the test_support borrow-split idiom).
    let mono = {
        let env = TypeCheckEnv::new(
            &tc.modules,
            &tc.next_id,
            &tc.module_aliases,
            &tc.prelude_fallback,
        );
        env.monomorphise_call(
            &mut tc.state,
            &Symbol::from("add"),
            &[Type::Int, Type::Int],
            Span::new(199, 208),
            None,
        )
        .unwrap()
        .expect("(add 1 2) must monomorphise")
    };

    // The mono body is the single variant's body. Every inferred_type on it
    // is concrete — that is the data the dropped `expr_types` side map held.
    let body = &mono.defn.variants.first().expect("mono has a variant").body;
    assert_types_concrete(body);

    // The `+` call site carries a concrete `resolved_call` directly on the
    // AST node — the data the dropped `resolutions` side map held.
    if let Expr::Apply { resolved_call, .. } = body {
        assert!(
            resolved_call.is_some(),
            "mono body's + call site must carry resolved_call on the AST node \
             (the dropped MethodResolutions side map is no longer the carrier)"
        );
    } else {
        panic!("mono body should be Apply, got {:?}", body);
    }
}

// spec: 07-traits §7.4 / design/typecheck/ast-annotation.md §9.4 — ≥2
// INSTANTIATIONS. A single generic (constrained) template called at TWO
// distinct concrete type sets mints TWO distinct mono instances, each a
// Concrete `Def` with the correct mangled key AND its own GOT slot. This is
// the crate-side mint-seam pin for the 0488 defect class (generic-fn missing
// monomorphisation at ≥2 instantiations) — it asserts the specific resolved
// facts (both keys minted, both Concrete, distinct slots), not "no panic".
#[test]
fn two_instantiations_mint_two_distinct_concrete_mono_entries() {
    let mut tc = tc_with_prims();
    register_num_for_int(&mut tc);
    register_num_impl_for_float(&mut tc);

    // Template: (defn add [x y] (+ x y)) — constrained on Num.
    let add_defn = TopLevel::Defn(Defn {
        name: Symbol::from("add"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None), (Symbol::from("y"), None)],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("+"), Span::new(18, 19))),
                args: vec![
                    Expr::var(Symbol::from("x"), Span::new(20, 21)),
                    Expr::var(Symbol::from("y"), Span::new(22, 23)),
                ],
                span: Span::new(17, 24),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 25),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 25),
    });
    tc.check_repl_input_self(&add_defn).unwrap();

    // First instantiation: (defn use-int [] (add 1 2))
    let use_int = TopLevel::Defn(Defn {
        name: Symbol::from("use-int"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add"), Span::new(200, 203))),
                args: vec![
                    Expr::IntLit { value: 1, span: Span::new(204, 205), inferred_type: None },
                    Expr::IntLit { value: 2, span: Span::new(206, 207), inferred_type: None },
                ],
                span: Span::new(199, 208),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(180, 209),
        }],
        visibility: Visibility::Public,
        span: Span::new(180, 209),
    });
    tc.check_repl_input_self(&use_int).unwrap();

    // Second instantiation at a DISTINCT type set: (defn use-float [] (add 1.5 2.5))
    let use_float = TopLevel::Defn(Defn {
        name: Symbol::from("use-float"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::var(Symbol::from("add"), Span::new(300, 303))),
                args: vec![
                    Expr::FloatLit { value: 1.5, span: Span::new(304, 307), inferred_type: None },
                    Expr::FloatLit { value: 2.5, span: Span::new(308, 311), inferred_type: None },
                ],
                span: Span::new(299, 312),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(280, 313),
        }],
        visibility: Visibility::Public,
        span: Span::new(280, 313),
    });
    tc.check_repl_input_self(&use_float).unwrap();

    // BOTH mono instances must be minted, each Concrete, under its own key.
    let int_slot = assert_concrete_mono_slot(&tc, "test/add$Int+Int");
    let float_slot = assert_concrete_mono_slot(&tc, "test/add$Float+Float");

    // Distinct instantiations get distinct GOT slots.
    assert_ne!(
        int_slot, float_slot,
        "the two mono instances must occupy distinct GOT slots"
    );
}

/// Assert `key` names a registered Concrete mono `Def` with a GOT slot; return
/// the slot. Shared by the ≥2-instantiations cell above.
fn assert_concrete_mono_slot(tc: &crate::checker::TestFixture, key: &str) -> usize {
    let st = tc.symbol_table();
    match st.get(key) {
        Some(entry @ ModuleEntry::Def { kind, ast, .. }) => {
            assert!(
                matches!(
                    kind.as_ref(),
                    DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }
                ),
                "mono '{key}' kind should be UserFn(Concrete), got {:?}",
                kind
            );
            assert!(ast.is_some(), "mono '{key}' must carry a compilable ast: Some(..)");
            entry
                .callable_got_slot()
                .unwrap_or_else(|| panic!("mono '{key}' must have a GOT slot assigned"))
        }
        other => panic!("mono '{key}' should be a Def entry, got {:?}", other),
    }
}
