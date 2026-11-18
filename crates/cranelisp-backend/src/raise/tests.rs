//! P-15 (`tests/plan/s123-evidence-delta.md` §3.2): no reachable code after a
//! raise. Each panic site's production emission is rendered and every call to
//! `runtime/panic` must be followed only by its block's trap terminator. The
//! census asserts that the raise helper is the only emitter of that call.

use std::path::{Path, PathBuf};

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use cranelisp_types::Span;

use super::{PANIC_SYMBOL, PanicHandle};
use crate::heap::HeapCategory;
use crate::jit::Jit;
use crate::test_support::assert_raise_terminates;

/// Render `(a, b) -> i64` whose body is `emit(builder, module, panic, a, b)`
/// in a module that declares only `runtime/panic`, as its catalog entry does.
fn render(
    emit: impl FnOnce(
        &mut FunctionBuilder,
        &mut crate::jit::FarCallModule,
        PanicHandle,
        Value,
        Value,
    ) -> Value,
) -> (String, FuncId) {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.far_call_module();
    let panic = PanicHandle::declare_alone(module);
    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));
    let mut fctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let (a, b) = (
        builder.block_params(entry)[0],
        builder.block_params(entry)[1],
    );
    let result = emit(&mut builder, module, panic, a, b);
    builder.ins().return_(&[result]);
    builder.seal_all_blocks();
    builder.finalize();
    (ctx.func.display().to_string(), panic.func_id())
}

// spec: design/backend/backend.md §7 "One emission helper" — the division
// guard's one raise (a zero divisor; `MIN / -1` wraps, spec §12.7.3)
// terminates its block.
#[test]
fn division_raise_ends_its_block() {
    let (clif, panic) = render(|builder, module, panic, a, b| {
        crate::primitives_inline::try_emit_inline_primitive(
            builder,
            "div-i64",
            &[a, b],
            Span::SYNTHETIC,
            module,
            Some(panic),
        )
        .expect("div-i64 is inline")
        .expect("div-i64 emits")
    });
    assert_eq!(
        assert_raise_terminates(&clif, panic, "div-i64"),
        1,
        "{clif}"
    );
}

// spec: design/backend/backend.md §7 "One Vec index guard" — the `vec-get`
// bounds raise terminates its block.
#[test]
fn vec_get_bounds_raise_ends_its_block() {
    let (clif, panic) = render(|builder, module, panic, vec, idx| {
        crate::compiler::vec_codegen::emit_vec_get_core(
            builder,
            module,
            panic,
            HeapCategory::AlwaysHeap,
            vec,
            idx,
            Span::SYNTHETIC,
        )
        .expect("emit vec-get")
    });
    assert_eq!(
        assert_raise_terminates(&clif, panic, "vec-get"),
        1,
        "{clif}"
    );
}

// spec: design/backend/backend.md §7 "Sites" — a match's failure block raises
// `"match failed"` and terminates, through the production per-body compile.
#[test]
fn match_failure_raise_ends_its_block() {
    use cranelisp_types::{
        Defn, DefnVariant, Expr, FQSymbol, MatchArm, ModuleFullPath, Pattern, Symbol, SymbolTable,
        Type, Visibility,
    };
    let int = |value| Expr::IntLit {
        value,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let body = Expr::Match {
        scrutinee: Box::new(int(1)),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard {
                span: Span::SYNTHETIC,
            },
            body: int(2),
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
        compiler_generated: false,
    };
    let defn = Defn {
        name: Symbol::from("match_raise_probe"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let user = ModuleFullPath::from("user");
    tables.insert(user.clone(), SymbolTable::new(user.clone()));
    let no_targets: std::collections::HashMap<Span, FQSymbol> = Default::default();
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let clif = crate::test_support::probe_defn_clif(
        &defn,
        &[],
        &no_targets,
        &tables,
        user,
        jit.jit_module(),
    );
    let panic = match jit.jit_module().get_name("runtime/panic") {
        Some(cranelift_module::FuncOrDataId::Func(id)) => id,
        other => panic!("runtime/panic is declared as a function, got {other:?}"),
    };
    assert_eq!(assert_raise_terminates(&clif, panic, "match"), 1, "{clif}");
    assert!(
        clif.contains("iconst.i64 12"),
        "the 12-byte \"match failed\" message\n{clif}"
    );
}

// ---------------------------------------------------------------------------
// The handle: only `raise` holds the declared id.
// ---------------------------------------------------------------------------

// spec: design/backend/backend.md §7 "No second path to the id" — the
// declaration loop hands `runtime/panic` to `raise`, so the by-name map that
// seeds every compile's `func_ids` does not contain it.
#[test]
fn the_declared_panic_is_held_only_as_the_handle() {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let ids = crate::jit::declare_intrinsics_generic(jit.jit_module()).expect("declare");
    assert!(ids.panic.is_some(), "the loop claims the panic funnel");
    assert!(
        !ids.by_name
            .contains_key(&cranelisp_types::Symbol::from(PANIC_SYMBOL)),
        "the by-name map must not yield the panic id"
    );
}

// spec: design/backend/backend.md §7 "No second path to the id" — `claim`
// wraps the panic funnel's entry and no other.
#[test]
fn claim_wraps_only_the_panic_entry() {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let declared = PanicHandle::declare_alone(jit.jit_module()).func_id();
    assert_eq!(
        super::claim(PANIC_SYMBOL, declared).map(PanicHandle::func_id),
        Some(declared)
    );
    assert!(super::claim("runtime/alloc", declared).is_none());
}

// ---------------------------------------------------------------------------
// Census: no production source outside `raise` names the panic funnel.
// ---------------------------------------------------------------------------

/// The file that holds the handle and the one raise emitter.
const RAISE_HOME: &str = "src/raise.rs";

/// Mentions of the panic funnel's name in `text`, outside comment lines. A
/// by-name declaration must spell it, and Cranelift answers a re-declaration
/// with the declared id, which would bypass the handle.
fn panic_symbol_mentions(text: &str) -> usize {
    text.lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .map(|line| line.matches(PANIC_SYMBOL).count())
        .sum()
}

fn is_test_source(path: &Path) -> bool {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or_default();
    name == "tests.rs"
        || name.ends_with("_tests.rs")
        || name == "test_support.rs"
        || name == "test_child.rs"
        || path.components().any(|c| c.as_os_str() == "tests")
}

fn production_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("read src dir") {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            production_sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") && !is_test_source(&path) {
            out.push(path);
        }
    }
}

// spec: design/arch/safety-invariants.md R13 — the handle makes reuse of the
// declared id unwritable outside `raise`; the residual is a by-name
// re-declaration, so no production source outside `raise` spells the name.
// Blind spot: a name that is computed and never spelled (backend.md §7).
#[test]
fn panic_symbol_is_named_only_in_raise() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    production_sources(&root.join("src"), &mut files);
    let offenders: Vec<String> = files
        .iter()
        .filter(|p| !p.ends_with(RAISE_HOME))
        .filter_map(|p| {
            let n = panic_symbol_mentions(&std::fs::read_to_string(p).expect("read source"));
            (n > 0).then(|| format!("{} ({n})", p.strip_prefix(root).unwrap_or(p).display()))
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "{PANIC_SYMBOL} named outside {RAISE_HOME}: {offenders:?}"
    );
    let home = std::fs::read_to_string(root.join(RAISE_HOME)).expect("read raise home");
    assert!(
        panic_symbol_mentions(&home) > 0,
        "{RAISE_HOME} names the funnel"
    );
}

// spec: design/arch/safety-invariants.md R13 — detection proof for the
// census: a planted by-name declaration is found; a comment and another
// intrinsic's declaration are not.
#[test]
fn panic_symbol_census_detects_a_planted_declaration() {
    let planted =
        "let id = module\n    .declare_function(\"runtime/panic\", Linkage::Import, &sig)?;";
    assert_eq!(panic_symbol_mentions(planted), 1);
    let silent = "// calls runtime/panic\n\
                  let id = module.declare_function(\"runtime/alloc\", Linkage::Import, &sig)?;";
    assert_eq!(panic_symbol_mentions(silent), 0);
}
