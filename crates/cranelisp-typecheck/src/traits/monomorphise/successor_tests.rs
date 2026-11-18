//! Successor discovery inside an instance
//! (`design/typecheck/monomorphisation.md` §3.10.5 module rows).

use cranelisp_types::{
    ApplyRef, CallableOrigin, FQSymbol, Life, ModuleFullPath, MonoDefnVariant, MonoExpr, VarRef,
};

use crate::checker::TestFixture;
use crate::program::test_support::{check_src, seed_specific_import, symbol_names_containing};
use crate::traits::test_helpers::*;

/// Check `src` as one cluster in the `test` module, which globs `primitives`.
fn checked(src: &str) -> TestFixture {
    let mut tc = tc_with_prims();
    check_src(&mut tc, src);
    tc
}

/// Every target a concrete body's codegen view calls or names as a value that
/// is not an installed concrete callable, whether a template or no table entry
/// at all: the condition the backend refuses as `undefined function`. A
/// nullary constructor is lowered from its constructor metadata, not called,
/// so it is not reported. An `Apply` with a `Dispatch` verdict is read by that
/// verdict, not its callee.
fn template_references(tc: &TestFixture) -> Vec<String> {
    let views: Vec<(String, MonoDefnVariant)> = tc
        .symbol_table()
        .all_symbols()
        .filter_map(|(name, binding)| {
            binding
                .codegen_view()
                .map(|view| (name.as_ref().to_string(), view.clone()))
        })
        .collect();
    let mut targets = Vec::new();
    for (name, view) in &views {
        reached_targets(&view.body, &mut |target| {
            targets.push((name.clone(), target.clone()))
        });
    }
    targets
        .into_iter()
        .filter(|(_, target)| {
            !tc.modules.get(&target.module).is_some_and(|table| {
                table
                    .get(target.symbol.as_ref())
                    .and_then(|binding| binding.callable())
                    .is_some_and(|callable| {
                        matches!(callable.arm.life, Life::Concrete { .. })
                            || matches!(
                                callable.origin,
                                CallableOrigin::Ctor { field_count: 0, .. }
                            )
                    })
            })
        })
        .map(|(name, target)| format!("{name} -> {target}"))
        .collect()
}

fn reached_targets(expr: &MonoExpr, found: &mut impl FnMut(&FQSymbol)) {
    match expr {
        MonoExpr::Var {
            resolution: VarRef::Global(target),
            ..
        } => found(target),
        MonoExpr::Apply {
            callee,
            args,
            dispatch,
            ..
        } => {
            match dispatch {
                ApplyRef::Dispatch(target) => found(target),
                ApplyRef::ViaCallee => reached_targets(callee, found),
            }
            args.iter().for_each(|arg| reached_targets(arg, found));
        }
        MonoExpr::Let { bindings, body, .. } | MonoExpr::ParBind { bindings, body, .. } => {
            bindings
                .iter()
                .for_each(|(_, value)| reached_targets(value, found));
            reached_targets(body, found);
        }
        MonoExpr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            reached_targets(cond, found);
            reached_targets(then_branch, found);
            reached_targets(else_branch, found);
        }
        MonoExpr::Lambda { body, .. } | MonoExpr::Trace { body, .. } => {
            reached_targets(body, found)
        }
        MonoExpr::Match {
            scrutinee, arms, ..
        } => {
            reached_targets(scrutinee, found);
            arms.iter()
                .for_each(|arm| reached_targets(&arm.body, found));
        }
        MonoExpr::VecLit { elements, .. } => {
            elements.iter().for_each(|e| reached_targets(e, found));
        }
        MonoExpr::ConstrADT { fields, .. } => {
            fields.iter().for_each(|e| reached_targets(e, found));
        }
        MonoExpr::LaunchContinue {
            launched,
            continuation,
            ..
        } => {
            reached_targets(launched, found);
            reached_targets(continuation, found);
        }
        _ => {}
    }
}

const OPT_SIZE: &str = "(deftype (Opt a) Nope (Yep [:a v]))\n\
                        (deftrait Size (size [self] Int))\n";

// spec: 07-traits §7.3.3; monomorphisation.md §3.10.2 row 3 — an
// implementation-method instance calling a generic function of its own
// cluster mints that function's instance (A3, one-cluster shape).
#[test]
fn impl_instance_mints_same_cluster_generic_callee() {
    let tc = checked(&format!(
        "{OPT_SIZE}(defn k7 [x] 7)\n\
         (impl Size (Opt a) (defn size [o] (match o [Nope 0 (Yep x) (k7 x)])))\n\
         (defn main [] (size (Yep 3)))"
    ));
    assert_eq!(template_references(&tc), Vec::<String>::new());
    assert!(!symbol_names_containing(&tc, "(test/k7 [primitives/Int]").is_empty());
}

// spec: 07-traits §7.3.3; monomorphisation.md §3.10.2 row 3 twin — the same
// same-cluster callee passed as a value from the instance is minted too.
#[test]
fn impl_instance_mints_same_cluster_generic_callee_used_as_value() {
    let tc = checked(&format!(
        "{OPT_SIZE}(defn k7 [x] 7)\n\
         (defn ap [f v] (f v))\n\
         (impl Size (Opt a) (defn size [o] (match o [Nope 0 (Yep x) (ap k7 x)])))\n\
         (defn main [] (size (Yep 3)))"
    ));
    assert_eq!(template_references(&tc), Vec::<String>::new());
    assert!(!symbol_names_containing(&tc, "(test/k7 [primitives/Int]").is_empty());
}

// spec: 08-modules §8.6.4; monomorphisation.md §3.10.2 row 4 — the window's
// template set is keyed by identity: an imported body naming a spelling the
// cluster also defines reaches its own module's template, not the cluster's.
#[test]
fn window_templates_are_selected_by_identity_not_spelling() {
    let mut tc = tf_prims();
    let lib = ModuleFullPath::from("lib");
    tc.set_current_module(lib.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    check_src(&mut tc, "(defn helper [x] 1)\n(defn gen [x] (helper x))");

    tc.set_current_module(ModuleFullPath::from("user"));
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    seed_specific_import(&mut tc, &lib, &["gen"]);
    check_src(
        &mut tc,
        "(defn helper [x] 2)\n(defn wrap [x] (gen x))\n(defn main [] (wrap 5))",
    );
    assert_eq!(template_references(&tc), Vec::<String>::new());
    assert!(!symbol_names_containing(&tc, "(lib/helper [primitives/Int]").is_empty());
    assert!(symbol_names_containing(&tc, "(user/helper [primitives/Int]").is_empty());
}

/// Check `src` as one cluster in the `test` module and return its outcome.
fn check(src: &str) -> Result<TestFixture, cranelisp_types::CranelispError> {
    let mut tc = tc_with_prims();
    let sexps = cranelisp_frontend::parse(src).expect("parse");
    let program = cranelisp_frontend::build_forms(&sexps).expect("build_forms");
    tc.check_program_self(&program).map(|_| tc)
}

/// Run `body` on a thread with the compile worker's stack (the default
/// spawned-thread size; `src/session_v4/lifecycle.rs` sets none).
fn on_worker_stack<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(body)
        .expect("spawn")
        .join()
        .expect("the mint chain must fit the compile worker's stack")
}

fn instances_of(tc: &TestFixture, template: &str) -> Vec<String> {
    symbol_names_containing(tc, &format!("({template} ["))
}

const OPT_SIZE_CONSTRAINED: &str = "(impl Size (Opt :Size a)\n\
    (defn size [o] (match o [Nope 0 (Yep x) (add-i64 1 (size x))])))\n";
const SIZE_INT: &str = "(impl Size Int (defn size [n] n))\n";

// spec: 07-traits §7.3.3; monomorphisation.md §3.10.1 row 1 — a constrained
// implementation whose instance dispatches to the same template at a nested
// type mints the inner instance and redirects the site (A1).
#[test]
fn dispatch_hop_to_the_same_template_mints_the_inner_instance() {
    let tc = checked(&format!(
        "{OPT_SIZE}{OPT_SIZE_CONSTRAINED}{SIZE_INT}(defn main [] (size (Yep (Yep 3))))"
    ));
    assert_eq!(template_references(&tc), Vec::<String>::new());
    assert_eq!(instances_of(&tc, "test/Size.size$test/Opt").len(), 2);
}

// spec: 07-traits §7.3.3; monomorphisation.md §3.10.1 row 1 twin — the hop
// to a different implementation's template (A2).
#[test]
fn dispatch_hop_to_another_implementation_mints_its_instance() {
    let tc = checked(&format!(
        "{OPT_SIZE}(deftype (Box a) (MkBox [:a v]))\n\
         (impl Size (Box :Size a) (defn size [b] (match b [(MkBox x) (add-i64 10 (size x))])))\n\
         {OPT_SIZE_CONSTRAINED}{SIZE_INT}(defn main [] (size (Yep (MkBox 3))))"
    ));
    assert_eq!(template_references(&tc), Vec::<String>::new());
    assert_eq!(instances_of(&tc, "test/Size.size$test/Box").len(), 1);
}

// spec: 07-traits §7.3.3; monomorphisation.md §3.10.1 row 2 — the dispatch
// hop from a free-function instance whose template an earlier run published
// (C3, imported shape).
#[test]
fn dispatch_hop_from_an_imported_free_function_instance() {
    let mut tc = tf_prims();
    let lib = ModuleFullPath::from("lib");
    tc.set_current_module(lib.clone());
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    check_src(
        &mut tc,
        &format!(
            "{OPT_SIZE}{OPT_SIZE_CONSTRAINED}{SIZE_INT}\
             (defn twice [x] (add-i64 (size x) (size x)))"
        ),
    );
    tc.set_current_module(ModuleFullPath::from("user"));
    seed_glob_import(&mut tc, &ModuleFullPath::from("primitives"));
    seed_specific_import(&mut tc, &lib, &["twice", "Yep"]);
    check_src(&mut tc, "(defn main [] (twice (Yep 3)))");
    assert_eq!(template_references(&tc), Vec::<String>::new());
    assert_eq!(instances_of(&tc, "lib/Size.size$lib/Opt").len(), 1);
}

const LEN: &str = "(deftype (L a) LNil (LCons [:a h :(L a) t]))\n\
                   (deftrait Len (len [self] Int))\n\
                   (impl Len (L a) (defn len [l] (match l [LNil 0 (LCons h t) (add-i64 1 (len t))])))\n";

// spec: 03-types §3.10; monomorphisation.md §3.10.3 row 5 — a dispatch to
// the instance's own key redirects to it and mints nothing further
// (T-1034-d).
#[test]
fn dispatch_to_the_instances_own_key_redirects_to_it() {
    let tc = checked(&format!(
        "{LEN}(defn main [] (len (LCons 1 (LCons 2 LNil))))"
    ));
    assert_eq!(template_references(&tc), Vec::<String>::new());
    assert_eq!(instances_of(&tc, "test/Len.len$test/L").len(), 1);
}

// spec: 03-types §3.10; monomorphisation.md §3.10.3 row 5 twin — a sibling
// member at the implementation's instantiation is minted and redirected, in
// both member orders (T-1034-e).
#[test]
fn sibling_member_at_the_same_instantiation_is_minted_in_either_order() {
    let size = "(defn size [o] (match o [Nope 0 (Yep x) 1]))";
    let describe = "(defn describe [o] (add-i64 4 (size o)))";
    for members in [format!("{size} {describe}"), format!("{describe} {size}")] {
        let tc = checked(&format!(
            "(deftype (Opt a) Nope (Yep [:a v]))\n\
             (deftrait Cont (size [self] Int) (describe [self] Int))\n\
             (impl Cont (Opt a) {members})\n\
             (defn main [] (describe (Yep \"s\")))"
        ));
        assert_eq!(template_references(&tc), Vec::<String>::new(), "{members}");
        assert_eq!(
            instances_of(&tc, "test/Cont.size$test/Opt").len(),
            1,
            "{members}"
        );
    }
}

/// The refusal's observable facts: a located type error at `site` in `src`,
/// whose definition identity is `template`, naming the limit.
fn assert_depth_refusal(src: &str, site: &str, template: &str) -> String {
    let error = match check(src) {
        Ok(_) => panic!("a non-terminating instantiation must be refused:\n{src}"),
        Err(error) => error,
    };
    let cranelisp_types::CranelispError::TypeError { message, location } = &error else {
        panic!("the refusal is a type error: {error:?}");
    };
    let start = src.rfind(site).expect("site in source") as u32;
    assert_eq!(location.span.start, start, "{message}");
    assert_eq!(
        location
            .fq
            .as_ref()
            .map(|fq| fq.symbol.as_ref().to_string()),
        Some(template.to_string()),
        "{message}"
    );
    assert!(
        message.contains("instantiation depth limit of 64"),
        "{message}"
    );
    message.clone()
}

const Q7_GROWING: &str = "(impl Size (Opt :Size a)\n\
    (defn size [o] (match o [Nope 0 (Yep x) (add-i64 1 (size (Yep o)))])))\n";

// spec: 03-types §3.10; monomorphisation.md §3.10.3 rows 6 and 9 — a growing
// re-entry is refused at the successor's site, directly, through a
// constrained helper and through two implementations, with one diagnostic
// shape; nothing on the chain is installed.
#[test]
fn growing_reentry_is_refused_by_every_route_with_one_diagnostic() {
    let direct = format!("{OPT_SIZE}{SIZE_INT}{Q7_GROWING}(defn main [] (size (Yep 3)))");
    let direct_message = assert_depth_refusal(&direct, "(size (Yep o))", "Size.size$test/Opt");

    let helper = format!(
        "{OPT_SIZE}{SIZE_INT}(defn wrap [:Size x] (size (Yep x)))\n\
         (impl Size (Opt :Size a) (defn size [o] (match o [Nope 0 (Yep x) (wrap o)])))\n\
         (defn main [] (size (Yep 3)))"
    );
    let helper_message = assert_depth_refusal(&helper, "(size (Yep x))", "wrap");

    let two_impls = format!(
        "{OPT_SIZE}{SIZE_INT}(deftype (Box a) (MkBox [:a v]))\n\
         (impl Size (Opt :Size a) (defn size [o] (match o [Nope 0 (Yep x) (size (MkBox o))])))\n\
         (impl Size (Box :Size a) (defn size [b] (match b [(MkBox x) (size (Yep b))])))\n\
         (defn main [] (size (Yep 3)))"
    );
    let two_message = assert_depth_refusal(&two_impls, "(size (Yep b))", "Size.size$test/Box");

    for message in [&direct_message, &helper_message, &two_message] {
        assert!(message.contains("first instantiated at"), "{message}");
    }
}

// spec: 03-types §3.10; monomorphisation.md §3.10.3 row 6 controls — a
// constant re-entry from `(Opt Bool)` mints `(Opt Int)` once and redirects to
// it; a chain that grows once then settles mints.
#[test]
fn constant_and_grow_once_reentries_mint() {
    let constant = checked(&format!(
        "{OPT_SIZE}{SIZE_INT}(impl Size Bool (defn size [b] 1))\n\
         (impl Size (Opt :Size a) (defn size [o] (match o [Nope (size (Yep 7)) (Yep x) (size x)])))\n\
         (defn main [] (size (Yep true)))"
    ));
    assert_eq!(template_references(&constant), Vec::<String>::new());
    assert_eq!(instances_of(&constant, "test/Size.size$test/Opt").len(), 2);

    let grow_once = checked(
        "(deftype (Opt a) Nope (Yep [:a v]))\n\
         (deftype (P a b) (MkP [:a l :b r]))\n\
         (deftrait F (f [self] Int))\n\
         (impl F (P a b) (defn f [p] (match p [(MkP l r) (f (MkP r (Yep 1)))])))\n\
         (defn main [] (f (MkP 1 true)))",
    );
    assert_eq!(template_references(&grow_once), Vec::<String>::new());
    assert_eq!(instances_of(&grow_once, "test/F.f$test/P").len(), 3);
}

/// Fixture D: `levels` nested `Opt`s built by a flat `let` chain, with the
/// `(Yep x)` arm going through `step`.
fn depth_program(levels: usize, implementation: &str) -> String {
    let bindings: Vec<String> = (0..levels)
        .map(|i| match i {
            0 => "v0 (Yep 0)".to_string(),
            _ => format!("v{i} (Yep v{})", i - 1),
        })
        .collect();
    format!(
        "{implementation}(defn main [] (let [{}] (size v{})))",
        bindings.join(" "),
        levels - 1
    )
}

fn fixture_d() -> String {
    format!("{OPT_SIZE}{SIZE_INT}{OPT_SIZE_CONSTRAINED}")
}

// spec: 03-types §3.10 (the depth limit is at least 64); monomorphisation.md
// §3.10.3 row 6 boundary — 64 implementation instantiations mint on the
// worker's stack, 65 are refused at the impl's `(size x)`.
#[test]
fn depth_boundary_64_mints_65_is_refused_on_the_worker_stack() {
    on_worker_stack(|| {
        let tc = check(&depth_program(64, &fixture_d())).expect("64 levels mint");
        assert_eq!(instances_of(&tc, "test/Size.size$test/Opt").len(), 64);
        assert_depth_refusal(
            &depth_program(65, &fixture_d()),
            "(size x)",
            "Size.size$test/Opt",
        );
    });
}

// spec: 03-types §3.10; monomorphisation.md §3.10.3 row 6 unit twin — two
// members calling each other at each level count one implementation
// instantiation per level: 64 levels (128 method instances) mint, 65 are
// refused (T-DEPTH-c).
#[test]
fn depth_counts_implementation_instantiations_not_method_instances() {
    let header = "(deftype (Opt a) Nope (Yep [:a v]))\n\
                  (deftrait Size (sa [self] Int) (sb [self] Int))\n\
                  (impl Size Int (defn sa [n] n) (defn sb [n] n))\n\
                  (impl Size (Opt :Size a) (defn sa [o] (sb o))\n\
                    (defn sb [o] (match o [Nope 0 (Yep x) (add-i64 1 (sa x))])))\n";
    on_worker_stack(move || {
        let program = |levels| depth_program(levels, header).replace("(size v", "(sa v");
        let tc = check(&program(64)).expect("64 levels of two members mint");
        assert_eq!(instances_of(&tc, "test/Size.sa$test/Opt").len(), 64);
        assert_eq!(instances_of(&tc, "test/Size.sb$test/Opt").len(), 64);
        let refused = check(&program(65)).err().expect("65 levels are refused");
        assert!(
            refused
                .to_string()
                .contains("instantiation depth limit of 64")
        );
    });
}

// spec: 03-types §3.10; 07-traits §7.1.4; monomorphisation.md §3.10.3 — the
// implementation instantiation is the type `self` takes, not the first type
// with the implementing type's head: 65 sibling members whose earlier
// parameters are `(Opt Mi)` chain at the one instantiation `(Opt Int)` and
// mint (ACT-1072).
#[test]
fn siblings_differing_in_an_earlier_parameter_of_the_implementing_head_count_once() {
    let members = 65;
    let types: String = (0..members)
        .map(|i| format!("(deftype M{i} MkM{i})\n"))
        .collect();
    let sigs: String = (0..members)
        .map(|i| format!(" (m{i} [:(Opt M{i}) d self] Int)"))
        .collect();
    let bodies: String = (0..members)
        .map(|i| match i + 1 {
            next if next < members => format!(" (defn m{i} [d o] (m{next} Nope o))"),
            _ => format!(" (defn m{i} [d o] 7)"),
        })
        .collect();
    let src = format!(
        "(deftype (Opt a) Nope (Yep [:a v]))\n{types}\
         (deftrait Size{sigs})\n\
         (impl Size (Opt a){bodies})\n\
         (defn main [] (m0 Nope (Yep 3)))"
    );
    // The same earlier parameter, fixed, before a growing `self` still counts.
    let growing = format!(
        "{OPT_SIZE}(deftrait G (g [:(Opt Int) d self] Int))\n\
         (impl G Int (defn g [d n] n))\n\
         (impl G (Opt :G a) (defn g [d o] (g d (Yep o))))\n\
         (defn main [] (g Nope (Yep 3)))"
    );
    on_worker_stack(move || {
        let tc = check(&src).unwrap_or_else(|e| panic!("one instantiation is refused: {e}"));
        assert_eq!(template_references(&tc), Vec::<String>::new());
        for i in [0, 64] {
            assert_eq!(
                instances_of(&tc, &format!("test/Size.m{i}$test/Opt")).len(),
                1,
                "m{i}"
            );
        }
        assert_depth_refusal(&growing, "(g d (Yep o))", "G.g$test/Opt");
    });
}

// spec: 03-types §3.10; monomorphisation.md §3.10.3 row 6 unit twin — two
// implementations alternating on one chain are refused at 65 instantiations
// in all, not at 64 of either.
#[test]
fn alternating_implementations_count_on_one_chain() {
    let header = format!(
        "{OPT_SIZE}{SIZE_INT}(deftype (Box a) (MkBox [:a v]))\n\
         (impl Size (Box :Size a) (defn size [b] (match b [(MkBox x) (add-i64 1 (size x))])))\n\
         {OPT_SIZE_CONSTRAINED}"
    );
    let program = move |levels: usize| {
        let bindings: Vec<String> = (0..levels)
            .map(|i| {
                let ctor = if i % 2 == 0 { "Yep" } else { "MkBox" };
                match i {
                    0 => format!("v0 ({ctor} 0)"),
                    _ => format!("v{i} ({ctor} v{})", i - 1),
                }
            })
            .collect();
        format!(
            "{header}(defn main [] (let [{}] (size v{})))",
            bindings.join(" "),
            levels - 1
        )
    };
    on_worker_stack(move || {
        check(&program(64)).expect("64 alternating instantiations mint");
        let refused = check(&program(65)).err().expect("65 in all are refused");
        assert!(
            refused
                .to_string()
                .contains("instantiation depth limit of 64")
        );
    });
}

// spec: 03-types §3.10; monomorphisation.md §3.10.3 row 6 unit twin — a
// member recurring at its own implementation instantiation through a
// method-level type variable counts each recurrence and is refused.
#[test]
fn method_level_reentry_at_one_instantiation_is_refused() {
    let src = format!(
        "{OPT_SIZE}(deftrait G (g [self :a x] Int))\n\
         (impl G Int (defn g [n x] (g n (Yep x))))\n\
         (defn main [] (g 1 0))"
    );
    on_worker_stack(move || {
        let refused = check(&src)
            .err()
            .expect("an unbounded method-level re-entry is refused");
        assert!(
            refused
                .to_string()
                .contains("instantiation depth limit of 64")
        );
    });
}

// spec: 03-types §3.10; monomorphisation.md §3.10.3 row 6 unit twin — a
// free-function instance on the chain does not count toward the depth.
#[test]
fn free_function_instances_ride_the_chain_without_counting() {
    let header = format!(
        "{OPT_SIZE}{SIZE_INT}(defn via [:Size x] (size x))\n\
         (impl Size (Opt :Size a) (defn size [o] (match o [Nope 0 (Yep x) (add-i64 1 (via x))])))\n"
    );
    on_worker_stack(move || {
        let tc = check(&depth_program(64, &header)).expect("64 levels through a helper mint");
        assert_eq!(instances_of(&tc, "test/Size.size$test/Opt").len(), 64);
    });
}

// spec: 07-traits §7.3.3; monomorphisation.md §3.10.1 row 7 — inside an
// instance, a dispatch already settled to a concrete target, a built-in
// intercept and an auto-curried partial application keep their verdicts and
// mint nothing new.
#[test]
fn settled_sites_inside_an_instance_mint_nothing() {
    let tc = checked(&format!(
        "{OPT_SIZE}{SIZE_INT}(defn ap [f v] (f v))\n\
         (impl Size (Opt a) (defn size [o] (match o [Nope (size 5)\n\
            (Yep x) (add-i64 (add-i64 1 2) (ap (add-i64 3) 4))])))\n\
         (defn main [] (size (Yep true)))"
    ));
    assert_eq!(template_references(&tc), Vec::<String>::new());
    assert_eq!(instances_of(&tc, "test/Size.size$test/Opt").len(), 1);
    assert!(symbol_names_containing(&tc, "add-i64 [").is_empty());
}

// spec: 03-types §3.10; monomorphisation.md §3.10.3 "Reading the
// implementation instantiation" — a conventional implementation entry's
// receiver is read from self's binding, and an entry whose receiver cannot be
// read is refused at the demand's site as an internal inconsistency rather than
// recorded as a higher-kinded (receiver-less) instantiation.
#[test]
fn unreadable_conventional_receiver_is_an_internal_inconsistency() {
    let tc = checked(&format!(
        "{OPT_SIZE}(impl Size (Opt a) (defn size [o] 1))\n(defn main [] (size (Yep 3)))"
    ));
    let module = ModuleFullPath::from("test");
    let size = cranelisp_types::FQTraitName::new(module.clone(), "Size".into());
    let opt = cranelisp_types::FQTypeName::new(module.clone(), "Opt".into());
    let opt_int = cranelisp_types::Type::ADT(opt.clone(), vec![cranelisp_types::Type::Int]);
    let signature =
        cranelisp_types::Type::Fn(vec![opt_int.clone()], Box::new(cranelisp_types::Type::Int));
    let entry = |symbol: &str| FQSymbol {
        module: module.clone(),
        symbol: symbol.into(),
    };
    let site = cranelisp_types::Span::new(3, 9);
    let env = tc.env();

    let read =
        env.implementing_type_at(&size, &opt, &entry("Size.size$test/Opt"), &signature, site);
    assert_eq!(read.expect("the receiver is self's binding"), opt_int);

    let refusals = [
        (
            entry("Size.missing$test/Opt"),
            signature.clone(),
            "no trait member names this implementation entry",
        ),
        (
            entry("Size.size$test/Opt"),
            cranelisp_types::Type::Fn(vec![], Box::new(cranelisp_types::Type::Int)),
            "self variable is not bound by the signature",
        ),
    ];
    for (template, signature, cause) in refusals {
        let error = env
            .implementing_type_at(&size, &opt, &template, &signature, site)
            .expect_err("an unreadable conventional receiver is refused");
        let cranelisp_types::CranelispError::CodegenError { message, location } = &error else {
            panic!("an internal inconsistency, not a user error: {error:?}");
        };
        assert!(message.starts_with("internal inconsistency"), "{message}");
        assert!(message.contains(cause), "{message}");
        assert!(message.contains(template.symbol.as_ref()), "{message}");
        assert_eq!(location.span, site, "{message}");
    }
}
