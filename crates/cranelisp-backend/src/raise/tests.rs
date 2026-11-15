//! P-15 (`tests/plan/s123-evidence-delta.md` §3.2): no reachable code after a
//! raise. Each panic site's production emission is rendered and every call to
//! `runtime/panic` must be followed only by its block's trap terminator. The
//! census asserts that the raise helper is the only emitter of that call.

use std::path::{Path, PathBuf};

use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_types::Span;

use crate::heap::HeapCategory;
use crate::jit::Jit;
use crate::test_support::assert_raise_terminates;

/// A JIT module that declares only `runtime/panic`, as its catalog entry
/// does: two parameters and no result.
fn module_with_panic() -> (Jit, FuncId) {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    let panic = module
        .declare_function("runtime/panic", Linkage::Import, &sig)
        .expect("declare runtime/panic");
    (jit, panic)
}

/// Render `(a, b) -> i64` whose body is `emit(builder, module, panic, a, b)`.
fn render(
    emit: impl FnOnce(
        &mut FunctionBuilder,
        &mut cranelift_jit::JITModule,
        FuncId,
        Value,
        Value,
    ) -> Value,
) -> (String, FuncId) {
    let (mut jit, panic) = module_with_panic();
    let module = jit.jit_module();
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
    (ctx.func.display().to_string(), panic)
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
            Some(HeapCategory::AlwaysHeap),
            vec,
            idx,
            Span::SYNTHETIC,
            false,
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
// Census: the raise helper is the only emitter of a call to runtime/panic.
// ---------------------------------------------------------------------------

/// The file that holds the one raise emitter.
const RAISE_HOME: &str = "src/raise.rs";

/// Each `declare_func_in_func(<first argument>` in `text` whose first argument
/// names a panic function id. Making a `FuncRef` for `runtime/panic` is the
/// step every call to it needs.
fn panic_func_refs(text: &str) -> usize {
    text.match_indices("declare_func_in_func(")
        .filter(|(at, needle)| {
            let rest = &text[at + needle.len()..];
            let arg = rest.split([',', ')']).next().unwrap_or_default();
            arg.contains("panic")
        })
        .count()
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

// spec: design/arch/s123-panics-and-environment.md §1.3 — the emitted half's
// falsifier is an emitted `runtime/panic` call followed by reachable code. No
// production source outside the raise helper's home makes a `FuncRef` for
// `runtime/panic`, so every call goes through the helper, which terminates.
#[test]
fn raise_helper_is_the_only_panic_call_emitter() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    production_sources(&root.join("src"), &mut files);
    let offenders: Vec<String> = files
        .iter()
        .filter(|p| !p.ends_with(RAISE_HOME))
        .filter_map(|p| {
            let n = panic_func_refs(&std::fs::read_to_string(p).expect("read source"));
            (n > 0).then(|| format!("{} ({n})", p.strip_prefix(root).unwrap_or(p).display()))
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "runtime/panic FuncRefs outside {RAISE_HOME}: {offenders:?}"
    );
    let home = std::fs::read_to_string(root.join(RAISE_HOME)).expect("read raise home");
    assert_eq!(
        panic_func_refs(&home),
        1,
        "{RAISE_HOME} holds exactly one runtime/panic emitter"
    );
}

// spec: design/arch/s123-panics-and-environment.md §1.3 — detection proof for
// the census: it finds a planted emitter in both spellings the crate uses, and
// does not count a FuncRef for another intrinsic.
#[test]
fn panic_call_census_detects_a_planted_emitter() {
    let planted = "let r = module.declare_func_in_func(panic_id, builder.func);\n\
                   let s = self\n    .module\n    .declare_func_in_func(self.ctx.panic_func_id.unwrap(), f);";
    assert_eq!(panic_func_refs(planted), 2);
    let other = "let r = module.declare_func_in_func(vec_drop_func_id, builder.func);";
    assert_eq!(panic_func_refs(other), 0);
}
