// Backend-unit CLIF guards for the S96 Chunk-C race/select node bake
// (`design/backend/io-trampoline.md §16`). `compile_select`/`compile_race`
// (`select.rs`) are name-matched at the `BuiltinFn` apply arm; these units pin
// the emitted `IO_TAG_SELECT` (= 6) node SHAPE at the CLIF layer, in the default
// lane, independent of the reactor/runtime (the end-to-end winner/loser-drop
// behaviour is the `tests/concurrency_cancellation.rs` /qa seam).
//
// Harness: compile a zero-arg `defn` whose body is `(race a b)` / `(select [..])`,
// with the call's `resolved_call` set directly to `BuiltinFn { name }` (the
// typecheck output the backend name-matches on). The branches are plain `int_lit`s
// — the tag bake does not depend on the branch shape, and the runtime semantics
// are covered e2e.

use crate::heap::HeapAdt;
use crate::jit::Jit;
use cranelisp_types::{
    Defn, DefnVariant, Expr, FQTypeName, ModuleFullPath, ResolvedCall, Span, Symbol, SymbolTable,
    Type, TypeName, Visibility,
};
use std::collections::HashMap;

fn node_bases_for_tag(clif: &str, tag: i64) -> Vec<String> {
    let tag_values: Vec<&str> = clif
        .lines()
        .filter_map(|line| {
            let (lhs, rhs) = line.trim().split_once(" = ")?;
            (rhs.trim() == format!("iconst.i64 {tag}")).then_some(lhs)
        })
        .collect();
    clif.lines()
        .filter_map(|line| {
            let code = line.split(';').next()?.trim();
            let (stored, address) = code
                .strip_prefix("store notrap aligned ")?
                .split_once(", ")?;
            if !tag_values.contains(&stored) {
                return None;
            }
            address
                .strip_suffix("+16")
                .map(std::string::ToString::to_string)
        })
        .collect()
}

fn assert_node_func_addr_store(clif: &str, tag: i64, offset: i32) {
    let func_values: Vec<&str> = clif
        .lines()
        .filter_map(|line| {
            let (lhs, rhs) = line.trim().split_once(" = ")?;
            rhs.starts_with("func_addr.i64 ").then_some(lhs)
        })
        .collect();
    let bases = node_bases_for_tag(clif, tag);
    let found = clif.lines().any(|line| {
        let code = line.split(';').next().unwrap_or(line).trim();
        let Some((stored, address)) = code
            .strip_prefix("store notrap aligned ")
            .and_then(|store| store.split_once(", "))
        else {
            return false;
        };
        func_values.contains(&stored)
            && bases
                .iter()
                .any(|base| address == format!("{base}+{offset}"))
    });
    assert!(
        found,
        "node tag {tag} must store its disposer func_addr at +{offset}; CLIF:\n{clif}"
    );
}

fn values_for_iconst(clif: &str, value: i64) -> Vec<&str> {
    let expected = format!("iconst.i64 {value}");
    clif.lines()
        .filter_map(|line| {
            let (lhs, rhs) = line.trim().split_once(" = ")?;
            (rhs.trim() == expected).then_some(lhs)
        })
        .collect()
}

fn assert_node_const_store(clif: &str, tag: i64, offset: i32, value: i64) {
    let stored_values = values_for_iconst(clif, value);
    let bases = node_bases_for_tag(clif, tag);
    let found = clif.lines().any(|line| {
        let code = line.split(';').next().unwrap_or(line).trim();
        let Some((stored, address)) = code
            .strip_prefix("store notrap aligned ")
            .and_then(|store| store.split_once(", "))
        else {
            return false;
        };
        stored_values.contains(&stored)
            && bases
                .iter()
                .any(|base| address == format!("{base}+{offset}"))
    });
    assert!(
        found,
        "node tag {tag} must store constant {value} at +{offset}; CLIF:\n{clif}"
    );
}

fn assert_node_payload_size(clif: &str, tag: i64, payload_size: usize) {
    let expected = format!("iconst.i64 {payload_size}");
    let size_values: Vec<&str> = clif
        .lines()
        .filter_map(|line| {
            let (lhs, rhs) = line.trim().split_once(" = ")?;
            (rhs.trim() == expected).then_some(lhs)
        })
        .collect();
    let bases = node_bases_for_tag(clif, tag);
    let found = clif.lines().any(|line| {
        let code = line.split(';').next().unwrap_or(line).trim();
        let Some((result, rhs)) = code.split_once(" = ") else {
            return false;
        };
        if !bases.iter().any(|base| base == result) {
            return false;
        }
        let Some(arguments) = rhs
            .strip_prefix("call ")
            .and_then(|call| call.split_once('('))
            .and_then(|(_, tail)| tail.strip_suffix(')'))
        else {
            return false;
        };
        size_values.contains(&arguments.trim())
    });
    assert!(
        found,
        "node tag {tag} must allocate payload size {payload_size}; CLIF:\n{clif}"
    );
}

fn int_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn io_int_type() -> Type {
    Type::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO")),
        vec![Type::Int],
    )
}

fn io_int_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(io_int_type())),
    }
}

fn io_string_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO")),
            vec![Type::String],
        ))),
    }
}

fn continuation_lit(input: Type) -> Expr {
    Expr::IntLit {
        value: 99,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Fn(vec![input], Box::new(io_int_type())))),
    }
}

fn vec_lit(elements: Vec<Expr>) -> Expr {
    Expr::VecLit {
        elements,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
            vec![io_int_type()],
        ))),
    }
}

/// An `(name args...)` call whose `resolved_call` is `BuiltinFn { name }` — the
/// shape typecheck produces for `race`/`select` (the `bind` precedent).
fn builtin_call(name: &str, args: Vec<Expr>) -> Expr {
    let n = Symbol::from(name);
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: n.clone(),
            span: Span::SYNTHETIC,
            resolved_call: Some(Box::new(ResolvedCall::BuiltinFn { name: n.clone() })),
            inferred_type: Some(Box::new(Type::Int)),
        }),
        args,
        span: Span::SYNTHETIC,
        resolved_call: Some(Box::new(ResolvedCall::BuiltinFn { name: n })),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// Compile a probe `defn` whose body is `body` and return its CLIF.
fn clif_of_body(body: Expr) -> String {
    // S111 R4 §1.3: probe rides the production per-body seam.
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");

    let name = Symbol::from("select_codegen_probe");
    let defn = Defn {
        name: name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let symbol_tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let module_path = ModuleFullPath::from("user");
    symbol_tables.insert(module_path.clone(), SymbolTable::new(module_path.clone()));
    let no_targets: HashMap<Span, cranelisp_types::FQSymbol> = HashMap::new();
    crate::test_support::probe_defn_clif(
        &defn,
        &[],
        &no_targets,
        &symbol_tables,
        module_path,
        jit.jit_module(),
    )
}

// spec: io-trampoline.md §16.4 — `(race a b)` bakes the one `IO_TAG_SELECT` (= 6)
// node over a 2-element branch Vec (the literal `6` at TAG_OFFSET).
#[test]
fn race_builds_select_node_tag_six() {
    let clif = clif_of_body(builtin_call("race", vec![io_int_lit(1), io_int_lit(2)]));
    assert!(
        clif.contains("iconst.i64 6"),
        "`race` must construct an IO_TAG_SELECT (tag 6) node; CLIF:\n{clif}"
    );
}

// spec: io-trampoline.md §16.4 — `(select [a b])` bakes the SAME `IO_TAG_SELECT`
// (= 6) node over its Vec-literal branch carrier.
#[test]
fn select_builds_select_node_tag_six() {
    let clif = clif_of_body(builtin_call(
        "select",
        vec![vec_lit(vec![io_int_lit(1), io_int_lit(2)])],
    ));
    assert!(
        clif.contains("iconst.i64 6"),
        "`select` must construct an IO_TAG_SELECT (tag 6) node; CLIF:\n{clif}"
    );
}

// spec: spec/10-io.md §10.12.9 item 4 + design/backend/io-trampoline.md §16.4 —
// a Select result ownership edge carries the canonical disposer for `a`.
#[test]
fn race_carries_result_disposer_only_for_owning_payload() {
    let scalar = clif_of_body(builtin_call("race", vec![io_int_lit(1), io_int_lit(2)]));
    let owning = clif_of_body(builtin_call(
        "race",
        vec![io_string_lit(1), io_string_lit(2)],
    ));
    assert_eq!(HeapAdt::payload_size(2), 24);
    assert_eq!(HeapAdt::field_offset(1), 32);
    assert_node_payload_size(&scalar, 6, HeapAdt::payload_size(2));
    assert_node_payload_size(&owning, 6, HeapAdt::payload_size(2));
    assert_node_const_store(&scalar, 6, HeapAdt::field_offset(1), 0);
    assert!(
        !scalar.contains("func_addr"),
        "Int result carries the zero disposer:\n{scalar}"
    );
    assert!(
        owning.contains("func_addr.i64"),
        "String result carries canonical drop glue:\n{owning}"
    );
    assert_node_func_addr_store(&owning, 6, HeapAdt::field_offset(1));
}

// spec: spec/10-io.md §10.12.9 item 4 + design/backend/io-trampoline.md §5.1 —
// Bind records disposal authority for the value passed to its continuation.
#[test]
fn bind_carries_inner_result_disposer_only_for_owning_payload() {
    let scalar = clif_of_body(builtin_call(
        "bind",
        vec![io_int_lit(1), continuation_lit(Type::Int)],
    ));
    let owning = clif_of_body(builtin_call(
        "bind",
        vec![io_string_lit(1), continuation_lit(Type::String)],
    ));
    assert_eq!(HeapAdt::payload_size(3), 32);
    assert_eq!(HeapAdt::field_offset(2), 40);
    assert_node_payload_size(&scalar, 2, HeapAdt::payload_size(3));
    assert_node_payload_size(&owning, 2, HeapAdt::payload_size(3));
    assert_node_const_store(&scalar, 2, HeapAdt::field_offset(2), 0);
    assert!(
        !scalar.contains("func_addr"),
        "Int Bind input carries the zero disposer:\n{scalar}"
    );
    assert!(
        owning.contains("func_addr.i64"),
        "String Bind input carries canonical drop glue:\n{owning}"
    );
    assert_node_func_addr_store(&owning, 2, HeapAdt::field_offset(2));
}

// spec: io-trampoline.md §16.9 — the structural no-regression guard: an ordinary
// program (no race/select) constructs NO IO_TAG_SELECT node.
#[test]
fn no_combinator_builds_no_select_node_neg() {
    let clif = clif_of_body(int_lit(7));
    assert!(
        !clif.contains("iconst.i64 6"),
        "an ordinary program must construct NO IO_TAG_SELECT (tag 6) node; CLIF:\n{clif}"
    );
}

// --- `sleep` — the runtime-symbol poll-leaf bake (S96 C4, reactor.md §2.18) -----
//
// `(sleep d)` lowers to an `IO_TAG_EFFECT_POLL` (= 4) node whose `code_ptr` is the
// RUNTIME symbol `runtime/sleep_pollfn` (`func_addr`-baked — the NON-GOT path, the
// genuinely-new C4 machinery). These units pin that bake at the CLIF layer in the
// default lane (the park-then-resume behaviour is the intrinsics/e2e seam).

// spec: reactor.md §2.18 — `(sleep d)` builds an IO_TAG_EFFECT_POLL (tag 4) node.
#[test]
fn sleep_builds_poll_node_tag_four() {
    let clif = clif_of_body(builtin_call("sleep", vec![int_lit(100)]));
    assert!(
        clif.contains("iconst.i64 4"),
        "`sleep` must construct an IO_TAG_EFFECT_POLL (tag 4) node; CLIF:\n{clif}"
    );
}

// spec: reactor.md §2.18 — the `code_ptr` is the RUNTIME symbol `runtime/sleep_pollfn`,
// resolved as a `Linkage::Import` + `func_addr`-baked (the non-GOT runtime-symbol
// path that distinguishes `compile_sleep` from `compile_poll_effect`'s GOT-slot
// load). The CLIF declares the external fn and takes its address. RED-on-revert: if
// `sleep` were routed through the GOT slot load (a `global_value` + `load`) instead,
// there would be no `func_addr` to a runtime symbol here.
#[test]
fn sleep_bakes_runtime_symbol_code_ptr_via_func_addr() {
    let clif = clif_of_body(builtin_call("sleep", vec![int_lit(100)]));
    assert!(
        clif.contains("func_addr"),
        "`sleep` must bake its poll-fn `code_ptr` via func_addr to the runtime \
         symbol (the non-GOT path); CLIF:\n{clif}"
    );
    assert!(
        clif.contains("sleep_pollfn") || clif.contains("u0:"),
        "`sleep`'s func_addr must reference the imported runtime/sleep_pollfn; \
         CLIF:\n{clif}"
    );
}

// spec: reactor.md §2.18 — the user arg is MILLISECONDS; the backend bakes
// `duration_nanos = d × 1_000_000` (the leaf works in nanos) via `imul_imm v,
// 1_000_000` (the immediate renders in hex: 1_000_000 = 0xf_4240).
#[test]
fn sleep_converts_milliseconds_to_nanos() {
    let clif = clif_of_body(builtin_call("sleep", vec![int_lit(100)]));
    assert!(
        clif.contains("imul_imm") && clif.to_lowercase().contains("f_4240"),
        "`sleep` must convert milliseconds → nanos via `imul_imm v, 1_000_000` \
         (0xf_4240); CLIF:\n{clif}"
    );
}

// spec: reactor.md §2.18 — the structural no-regression guard: an ordinary program
// (no sleep / no poll effect) constructs NO IO_TAG_EFFECT_POLL node and bakes no
// runtime-symbol func_addr.
#[test]
fn no_sleep_builds_no_poll_node_neg() {
    let clif = clif_of_body(int_lit(7));
    assert!(
        !clif.contains("iconst.i64 4"),
        "an ordinary program must construct NO IO_TAG_EFFECT_POLL (tag 4) node; CLIF:\n{clif}"
    );
    assert!(
        !clif.contains("func_addr"),
        "an ordinary program must bake NO runtime-symbol func_addr; CLIF:\n{clif}"
    );
}
