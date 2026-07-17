//! Relocated crate-root JIT disasm/CLIF-capture tests (FIXME 0495 step 1): `produce_disasm` non-empty body + the `capture_clif` flag gate. Verbatim relocation from `src/tests.rs`.

use crate::test_support::*;


// spec: facades/backend.md §"Free functions" — produce_disasm reads the
// live GOT-slot code pointer, reads caller-supplied `code_size` bytes, and
// capstone-disassembles them (S75 W3 Finding-C — real body, not a stub).
#[test]
fn produce_disasm_returns_nonempty_for_jit_compiled_fn() {
    use cranelisp_types::FQSymbol;

    let defn = Defn {
        name: Symbol::from("seven"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::IntLit { value: 7, span: Span::new(0, 1), inferred_type: None },
            span: Span::new(0, 20),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 20),
    };

    let module = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(module.clone());
        st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
        st.next_got_slot = 1;
        tables.insert(module.clone(), st);
    }

    let mut jit = Jit::new_with_symbols(&[]).unwrap();
    let artifacts = compile_to_module(
        module.clone(),
        std::slice::from_ref(&defn.name),
        &tables,
        jit.jit_module(),
        true,
    ).expect("JIT compile should succeed");

    // code_size comes from the compile-time artifacts — the caller passes
    // it back into produce_disasm (Finding-C: backend never re-derives it).
    assert!(artifacts.code_size > 0, "JIT codegen must report a code size");

    let fq = FQSymbol { module: module.clone(), symbol: defn.name.clone() };
    let disasm = produce_disasm(&fq, artifacts.code_size, &tables)
        .expect("produce_disasm should disassemble live JIT code");
    assert!(
        !disasm.trim().is_empty(),
        "produce_disasm must return non-empty disassembly text for a live fn"
    );
}


// spec: design/arch/facades/backend.md — `capture_clif` flag (FIXME 0325)
//
// The `capture_clif: bool` parameter (FIXME 0325) gates whether
// `compile_to_module` populates `CompilationArtifacts.clif_ir` with the
// CLIF-IR text. `false` skips the `format!("{}", func.display())` work and
// leaves `clif_ir` empty; `true` captures it. This test compiles the same
// fixture under both states and asserts they differ — if the flag were
// ignored, the two `clif_ir` strings would match and the test fails.
//
// A fresh JIT + symbol-table pair is built per call because
// `compile_to_module` finalizes the module and writes the GOT slot.
#[test]
fn capture_clif_gates_clif_ir_text() {
    fn compile_once(capture_clif: bool) -> CompilationArtifacts {
        let defn = Defn {
            name: Symbol::from("answer"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
                span: Span::new(0, 10),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 10),
        };

        let module = ModuleFullPath::from("user");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(defn.name.clone(), make_def_entry_slot(defn.clone(), 0));
            st.next_got_slot = 1;
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new_with_symbols(&[]).unwrap();
        compile_to_module(
            module,
            std::slice::from_ref(&defn.name),
            &tables,
            jit.jit_module(),
            capture_clif,
        )
        .expect("direct compile_to_module should succeed")
    }

    // capture_clif = false: the CLIF text is not generated.
    let without = compile_once(false);
    assert!(
        without.clif_ir.is_empty(),
        "capture_clif = false must leave CompilationArtifacts.clif_ir empty, got: {:?}",
        without.clif_ir
    );

    // capture_clif = true: the CLIF text is captured.
    let with = compile_once(true);
    assert!(
        !with.clif_ir.is_empty(),
        "capture_clif = true must populate CompilationArtifacts.clif_ir"
    );

    // The compiled native code is unaffected by the flag — code_size is
    // produced in both cases (the flag only gates the CLIF *text*).
    assert!(
        without.code_size > 0 && with.code_size > 0,
        "code_size must be produced regardless of capture_clif"
    );
}
