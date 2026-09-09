//! Emitted apply-argument create-gate fences.
//!
//! These probes use the production multi-defn body seam so M-static direct
//! self-recursion reaches the same apply lowering as an ordinary module body.

use crate::jit::Jit;
use cranelisp_types::{Defn, DefnVariant, Expr, ModuleFullPath, Span, Symbol, Type, Visibility};

fn int(value: i64, span: Span) -> Expr {
    Expr::IntLit {
        value,
        span,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn var(name: &str, span: Span) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn call(name: &str, args: Vec<Expr>, span: Span) -> Expr {
    Expr::Apply {
        callee: Box::new(var(name, Span::new(span.start + 1, span.start + 2))),
        args,
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn defn(name: &str, body: Expr) -> Defn {
    Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("n"), None)],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

fn emitted_apply_gate_pair() -> (String, String) {
    // Both outer calls are non-tail. Their recursive `single`/`pair` arguments
    // are M-static candidates; only the pair clears the shared >=2 gate.
    let single = defn(
        "single",
        call(
            "sink",
            vec![
                call(
                    "single",
                    vec![var("n", Span::new(11, 12))],
                    Span::new(10, 13),
                ),
                int(7, Span::new(14, 15)),
            ],
            Span::new(1, 16),
        ),
    );
    let pair = defn(
        "pair",
        call(
            "sink",
            vec![
                call("pair", vec![var("n", Span::new(31, 32))], Span::new(30, 33)),
                call("pair", vec![var("n", Span::new(35, 36))], Span::new(34, 37)),
            ],
            Span::new(20, 38),
        ),
    );
    let sink = Defn {
        name: Symbol::from("sink"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("left"), None), (Symbol::from("right"), None)],
            body: int(0, Span::SYNTHETIC),
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let module_path = ModuleFullPath::from("user");
    let tables: dashmap::DashMap<ModuleFullPath, cranelisp_types::SymbolTable> =
        dashmap::DashMap::new();
    let mut table = cranelisp_types::SymbolTable::new(module_path.clone());
    for (name, arity) in [("single", 1), ("pair", 1), ("sink", 2)] {
        crate::test_support::insert_user_fn_stub(&mut table, name, arity);
    }
    tables.insert(module_path.clone(), table);

    let mut targets =
        crate::test_support::call_carriers(single.body(), &module_path, &["single", "sink"]);
    targets.extend(crate::test_support::call_carriers(
        pair.body(),
        &module_path,
        &["pair", "sink"],
    ));
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let clifs = crate::test_support::compile_defns_in_module(
        &[&single, &pair],
        &[&sink],
        &targets,
        &tables,
        module_path,
        jit.jit_module(),
    );
    (clifs[0].clone(), clifs[1].clone())
}

// spec: design/backend/lenient-eval.md §2.5 + §3.6.2 — one eligible
// apply argument remains sequential; the >=2 create gate must be absent.
#[test]
fn singleton_recursive_apply_argument_emits_no_create_gate() {
    let (single, _) = emitted_apply_gate_pair();
    assert!(
        !single.contains("brif"),
        "one recursive apply argument plus a literal must not emit a create gate:\n{single}"
    );
    assert!(
        !single.contains("iconst.i64 2"),
        "the singleton subject must not reserve two spark permits:\n{single}"
    );
}

// spec: design/backend/lenient-eval.md §2.5 + §3.6.2 — two eligible,
// non-tail recursive apply arguments reserve two permits and emit both gate arms.
#[test]
fn pair_recursive_apply_arguments_emits_the_create_gate_and_spark_arm() {
    let (_, pair) = emitted_apply_gate_pair();
    let gate_branch = pair
        .lines()
        .find(|line| line.trim_start().starts_with("brif "))
        .expect("create-gate branch in CLIF");
    let before_gate_branch = pair
        .split_once(gate_branch)
        .expect("CLIF before create-gate branch")
        .0;
    assert!(
        before_gate_branch.contains("iconst.i64 2"),
        "two recursive apply arguments must reserve two permits then branch:\n{pair}"
    );
    assert!(
        before_gate_branch.contains("call "),
        "the permit reservation must call the runtime gate before branching:\n{pair}"
    );

    // CLIF has opaque function refs, so prove the production create→spark data
    // path instead of counting all calls (which also sees the direct arm and RC
    // cleanup). The create-gate's false target is the direct arm; every
    // func_addr materialization before it must pass its closure to the first
    // call, then pass that IVar result to the next call.
    let direct_target = gate_branch
        .rsplit_once(", ")
        .map(|(_, target)| target.trim())
        .expect("direct-arm target in create-gate branch");
    let direct_marker = format!("\n{direct_target}:");
    let after_gate = pair
        .split_once(gate_branch)
        .expect("CLIF after create-gate branch")
        .1;
    let (lenient_arm, direct_arm) = after_gate
        .split_once(&direct_marker)
        .expect("direct arm after lenient spark arm");
    let lines: Vec<_> = lenient_arm.lines().map(str::trim).collect();
    let thunk_sites: Vec<_> = lines
        .iter()
        .enumerate()
        .filter_map(|(idx, line)| line.contains(" = func_addr.i64 ").then_some(idx))
        .collect();
    assert_eq!(
        thunk_sites.len(),
        2,
        "two eligible arguments must materialize two spark thunks:\n{pair}"
    );
    assert!(
        !direct_arm.contains("func_addr.i64"),
        "the direct arm must remain sequential, without spark thunks:\n{pair}"
    );
    for (position, &start) in thunk_sites.iter().enumerate() {
        let end = thunk_sites
            .get(position + 1)
            .copied()
            .unwrap_or(lines.len());
        let thunk_value = lines[start]
            .split_once(" = func_addr.i64 ")
            .map(|(value, _)| value)
            .expect("spark-thunk address result");
        let closure_value = lines[start..end]
            .iter()
            .find_map(|line| {
                if !line.contains(thunk_value) {
                    return None;
                }
                let (_, stored_at) = line.split_once(", ")?;
                Some(stored_at.split_once('+')?.0.trim())
            })
            .expect("spark thunk stored in its closure");
        let calls: Vec<_> = lines[start..end]
            .iter()
            .filter_map(|line| {
                let (result, call) = line.split_once(" = call ")?;
                let args = call.split_once('(')?.1.strip_suffix(')')?;
                Some((result, args))
            })
            .take(2)
            .collect();
        assert_eq!(
            calls.len(),
            2,
            "each thunk must be created then sparked:\n{pair}"
        );
        assert_eq!(
            calls[0].1, closure_value,
            "the first spark-path call must create an IVar from its thunk:\n{pair}"
        );
        assert_eq!(
            calls[1].1, calls[0].0,
            "the second spark-path call must spark the created IVar:\n{pair}"
        );
    }
}
