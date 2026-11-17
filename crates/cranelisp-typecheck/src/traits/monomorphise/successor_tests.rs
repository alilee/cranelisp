//! Successor discovery inside an instance
//! (`design/typecheck/monomorphisation.md` §3.10.5 module rows).

use cranelisp_types::{
    ApplyRef, FQSymbol, Life, ModuleFullPath, MonoDefnVariant, MonoExpr, TemplateBody, VarRef,
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

/// Every authored template a concrete body's codegen view calls or names as a
/// value: the condition the backend refuses as `undefined function`. An
/// `Apply` with a `Dispatch` verdict is read by that verdict, not its callee.
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
            tc.modules.get(&target.module).is_some_and(|table| {
                table
                    .get(target.symbol.as_ref())
                    .and_then(|binding| binding.callable())
                    .is_some_and(|callable| {
                        matches!(
                            callable.arm.life,
                            Life::Template {
                                body: TemplateBody::Ast(_),
                                ..
                            }
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
