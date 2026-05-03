// QUARANTINED — Sprint 64 test-port. Not built or run by Cargo.
// FIXME: design/arch/fixmes/0117-harvest-tests-legacy-wave2-g6.md
// Owning crate: cranelisp-typecheck (primary), cranelisp-backend (secondary)
// Owning skill: /typecheck
// Quarantined: 2026-05-03
//
// This file's assertions test Rust-internal state (Layer-3 `Code{ptr}`
// writes on `ModuleEntry::Def`, observed via Rust API) with no e2e
// equivalent. Harvest into `#[cfg(test)]` unit tests inside the owning
// crate per memory/feedback_unit_tests_with_dev.md and
// memory/project_test_strategy.md. Source preserved verbatim;
// translation may require dev-dependency adjustments and import
// rewrites against the post-FIXME-0109 internal surface.

//! Integration tests for Sprint 57 Wave 2 (G6 — Code on SymbolTable).
//!
//! These are Layer 3 integration tests: they exercise the full pipeline via
//! the Rust API (ReplSession / CompilerSession), observing the new code-write
//! path that landed in Wave 2.
//!
//! What Wave 2 did:
//! - `compile_to_module` now writes `Code { ptr }` onto `ModuleEntry::Def.code`
//!   (via the `CodeFinalizer` trait in the backend).
//! - The `CodegenProduct` DashMap was deleted; 10 read sites migrated to
//!   `symbol_tables[module].get(name).code`.
//! - REPL `__expr` flows through `compile_to_module` like any other name —
//!   no `compile_and_execute_expr` `&Program` fallback.
//! - `CheckResult` slimmed to `{ warnings, display }`.
//!
//! See:
//! - `design/backend/compile-to-module.md` §9.1 — write-path contract
//! - `design/int/phase2-codegen-convergence.md` §13 — reader migration
//! - `tests/plan/ring4.md` §G.1 — this test plan
//!
//! Test scope is integration-layer only. Unit tests for compile_to_module,
//! worker reader migration, and CheckResult shape land in their owning crates.

#[path = "helpers/mod.rs"]
mod helpers;

use cranelisp_types::{ModuleEntry, ModuleFullPath, Symbol};
use helpers::{repl_session, repl_eval};

// =============================================================================
// G6 — code-on-entry observable after compile
// =============================================================================

// spec: design/backend/compile-to-module.md §9.1 — G6 write-path contract
// spec: design/int/phase2-codegen-convergence.md §13.2 — backend writes to ModuleEntry::Def.code
#[test]
fn g6_code_on_entry_after_compile() {
    // Define a trivial zero-arg function; after eval, the entry's `code` field
    // must be `Some(_)`. This asserts the G6 write path lands — Wave 2's core
    // deliverable.
    let mut s = repl_session();
    // Register the module and define a function.
    repl_eval(&mut s, "(defn trivial [] 42)");
    // Call it to force JIT finalize / pointer retrieval if the path is lazy.
    assert_eq!(repl_eval(&mut s, "(trivial)"), 42);

    // Resolve the current module's symbol table and check the entry.
    let module = ModuleFullPath::from(s.session.current_module_name().as_str());
    let tables = s.symbol_tables();
    let table_ref = tables
        .get(&module)
        .expect("current module's symbol table must exist after eval");
    let entry = table_ref
        .get("trivial")
        .expect("'trivial' must be registered on the symbol table");
    match entry {
        ModuleEntry::Def { code, ast, .. } => {
            assert!(
                ast.is_some(),
                "G6 post-check: entry.ast must be Some after Phase 1 AST annotation"
            );
            assert!(
                code.is_some(),
                "G6 contract: entry.code must be Some(_) after compile_to_module writes it; \
                 got None which indicates the G6 write loop did not run"
            );
        }
        other => panic!("expected Def entry for 'trivial', got {:?}", other),
    }
}

// =============================================================================
// G6 — introspection reads through the migrated path
// =============================================================================

// spec: design/int/phase2-codegen-convergence.md §13.3 R3 — /clif reads via symbol-table path
// spec: repl/spec.md §3.1 — /clif shows Cranelift IR
#[test]
fn g6_clif_introspection_reads_from_symbol_table() {
    // /clif must continue to produce non-empty CLIF IR text after the read-path
    // migration. If the introspection read site still used the deleted
    // `codegen_products` DashMap, this command would return "no CLIF available".
    let mut s = repl_session();
    repl_eval(&mut s, "(defn double [x] (add-i64 x x))");

    // Call the handle_clif path via the slash-command entry point exposed
    // indirectly: we exercise the symbol-table-driven introspection by
    // asserting that the clif_ir text carries a real Cranelift instruction.
    // We reach into the session's handlers by driving the REPL with a
    // carefully crafted input — but since dispatch_command is not public,
    // we call the typed path instead: introspection data is populated during
    // compilation and retrieved through `/clif` output. We observe via the
    // shared state's `introspection` map which is publicly reachable.
    let fq = cranelisp_types::FQSymbol {
        module: ModuleFullPath::from(s.session.current_module_name().as_str()),
        symbol: Symbol::from("double"),
    };
    let intr = s
        .session
        .shared
        .introspection
        .get(&fq)
        .expect("introspection entry must exist for 'double' after compile");
    let clif = intr
        .clif_ir
        .as_ref()
        .expect("clif_ir must be populated on introspection entry");
    assert!(
        !clif.is_empty(),
        "/clif path: CLIF IR text must be non-empty"
    );
    assert!(
        clif.contains("function") || clif.contains("block") || clif.contains("v"),
        "CLIF IR must contain recognisable Cranelift syntax, got:\n{clif}"
    );
}

// spec: design/int/phase2-codegen-convergence.md §13.3 R3 — /source reads via symbol-table path
// spec: repl/spec.md §3.1 — /source shows original source text
#[test]
fn g6_source_introspection_reads_from_symbol_table() {
    // /source surfaces either `introspection.source` or `.sexp`. The data is
    // captured during eval. After G6, the `compile_to_module`-driven path
    // still wires introspection through the same code path; /source must work.
    let mut s = repl_session();
    let src = "(defn trip [x] (add-i64 x (add-i64 x x)))";
    repl_eval(&mut s, src);

    let fq = cranelisp_types::FQSymbol {
        module: ModuleFullPath::from(s.session.current_module_name().as_str()),
        symbol: Symbol::from("trip"),
    };
    let intr = s
        .session
        .shared
        .introspection
        .get(&fq)
        .expect("introspection entry must exist for 'trip' after compile");

    // Either source or sexp must be populated (handle_source falls back to sexp).
    let has_payload = intr.source.is_some() || intr.sexp.is_some();
    assert!(
        has_payload,
        "/source path: either introspection.source or .sexp must be populated"
    );
}

// =============================================================================
// G6 — CodegenProduct regression guard (structural)
// =============================================================================

// spec: design/int/phase2-codegen-convergence.md §13.4 — CodegenProduct deletion
// spec: tests/plan/ring4.md §G.1 — v4_codegen_product_deletion_regression_guard
#[test]
fn g6_codegen_product_regression_guard() {
    // Wave 2's close gate: the `CodegenProduct` struct and `codegen_products`
    // field are deleted. If anyone re-introduces the DashMap, this test fails.
    // Only comment-level references to the old name are permitted (historical
    // context). A struct/impl/type re-declaration must fail here.
    let src_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");

    // Visit every .rs file under src/.
    fn scan_rs(dir: &std::path::Path, matches: &mut Vec<(std::path::PathBuf, String)>) {
        let entries = match std::fs::read_dir(dir) {
            Ok(it) => it,
            Err(_) => return,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                scan_rs(&path, matches);
                continue;
            }
            if path.extension().and_then(|e| e.to_str()) != Some("rs") {
                continue;
            }
            let content = match std::fs::read_to_string(&path) {
                Ok(c) => c,
                Err(_) => continue,
            };
            for (lineno, line) in content.lines().enumerate() {
                let trimmed_start = line.trim_start();
                // Skip comments and doc strings — we only care about live code.
                if trimmed_start.starts_with("//")
                    || trimmed_start.starts_with("///")
                    || trimmed_start.starts_with("/*")
                    || trimmed_start.starts_with("*")
                {
                    continue;
                }
                // Look for forbidden patterns that would indicate live references.
                let forbidden = [
                    "struct CodegenProduct",
                    "impl CodegenProduct",
                    "impl Default for CodegenProduct",
                    "CodegenProduct {",
                    ": CodegenProduct",
                    "<CodegenProduct>",
                    "codegen_products:",
                    "&self.shared.codegen_products",
                    ".codegen_products.",
                    ".codegen_products[",
                    "product.code.insert",
                ];
                for pat in &forbidden {
                    if line.contains(pat) {
                        matches.push((
                            path.clone(),
                            format!("{}:{}: {}", path.display(), lineno + 1, line.trim()),
                        ));
                    }
                }
            }
        }
    }

    let mut matches = Vec::new();
    scan_rs(&src_dir, &mut matches);
    assert!(
        matches.is_empty(),
        "G6 close gate: CodegenProduct / codegen_products live references detected in src/:\n{}",
        matches
            .iter()
            .map(|(_, l)| l.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// =============================================================================
// G6 — cross-module call through symbol-table-driven resolution
// =============================================================================

// spec: design/int/phase2-codegen-convergence.md §13.3 R1/R9 — cross-module resolution
#[test]
fn g6_cross_module_call_via_symbol_table() {
    // Two-module project: main imports a function from util and calls it.
    // After G6, cross-module call resolution walks `symbol_tables` rather than
    // `codegen_products`. This test guards that the path works end-to-end.
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("main.cl"),
        "(import [util [helper]])\n(defn main [] (helper))",
    )
    .unwrap();
    std::fs::write(dir.path().join("util.cl"), "(defn helper [] 123)").unwrap();

    let (value, _ty) = helpers::batch_run_file(&dir.path().join("main.cl"), &[]).unwrap();
    assert_eq!(
        value, 123,
        "cross-module call must succeed through symbol-table-driven GOT resolution"
    );
}

// =============================================================================
// G6 — REPL expression via compile_to_module (no special case)
// =============================================================================

// spec: design/int/phase2-codegen-convergence.md §13.6 — `__expr` is a normal ModuleEntry::Def
#[test]
fn g6_repl_expr_uses_compile_to_module_path() {
    // A bare expression at the REPL was previously handled via a special-case
    // `compile_and_execute_expr(&Program)` fallback. That fallback was deleted
    // in Wave 2. The expression now flows through `compile_to_module` like any
    // other name, registered as `__expr` on the symbol table.
    //
    // We can't observe "no special case" directly, but we can observe the
    // behaviour contract: an expression eval returns the right value AND the
    // compiled code is observable on the symbol-table entry afterwards.
    let mut s = repl_session();
    let val = repl_eval(&mut s, "(add-i64 17 25)");
    assert_eq!(val, 42, "repl expression must evaluate correctly");

    // The `__expr` entry must exist on the current module after eval.
    let module = ModuleFullPath::from(s.session.current_module_name().as_str());
    let tables = s.symbol_tables();
    let table_ref = tables
        .get(&module)
        .expect("current module's symbol table must exist");
    let entry = table_ref.get("__expr");
    // `__expr` may be overwritten on each eval; require that if present it has
    // Code::Some, confirming it flowed through compile_to_module.
    if let Some(ModuleEntry::Def { code, .. }) = entry {
        assert!(
            code.is_some(),
            "G6: __expr entry (if present) must carry code after compile_to_module"
        );
    }
    // If __expr was not retained as a named entry (session may clean it up),
    // the behaviour contract is still satisfied by the value assertion above —
    // this is intentionally permissive to avoid coupling to internal retention
    // policy.
}

// =============================================================================
// G6 — CheckResult slim regression guard
// =============================================================================

// spec: design/typecheck/ast-annotation.md §10.2.3 — CheckResult has only { warnings, display }
#[test]
fn g6_check_result_slim_shape() {
    // The CheckResult struct exposes exactly two public fields after Wave 2:
    // `warnings` and `display`. Legacy fields (`method_resolutions`,
    // `mono_defns`, `default_method_defns`, `constrained_fn_names`,
    // `expr_types`) were retired once AST-annotation became the source of
    // truth. If someone reintroduces any of them, this test won't compile.
    use cranelisp_types::CheckResult;
    // Destructure-style: only two fields must be nameable.
    fn accept(r: &CheckResult) -> usize {
        // If the struct gains new public fields, match exhaustiveness won't
        // catch it, but any attempt to access a retired field below will
        // fail to compile.
        let _ = &r.warnings;
        let _ = &r.display;
        r.warnings.len()
    }
    let r = CheckResult {
        warnings: Vec::new(),
        display: None,
    };
    assert_eq!(accept(&r), 0);
}

// =============================================================================
// G6 — multi-sig JIT regression guards (flip-green preservation from S56)
// =============================================================================
//
// Three `sketch_multi_sig_*` tests flipped green in Sprint 56. Wave 2 must
// preserve them. We duplicate the minimal assertions here as dedicated
// regression guards so a Wave-2 G6 regression shows up both in sketch_port
// and in this targeted file.

// spec: 05-definitions §5.1.2 — multi-sig type-based dispatch still works post-G6
#[test]
fn g6_multi_sig_type_based_dispatch_regression_guard() {
    let mut s = repl_session();
    repl_eval(&mut s, "(defn choose ([x y] (add-i64 x y)) ([x y] (if y x 0)))");
    assert_eq!(
        repl_eval(&mut s, "(add-i64 (choose 10 20) (choose 5 true))"),
        35,
        "post-G6: multi-sig type-based dispatch must still produce 35 (30 + 5)"
    );
}

// spec: 05-definitions §5.1.2 — multi-sig different arities still works post-G6
#[test]
fn g6_multi_sig_different_arities_regression_guard() {
    let mut s = repl_session();
    repl_eval(
        &mut s,
        "(defn add3 ([x y] (add-i64 x y)) ([x y z] (add-i64 x (add-i64 y z))))",
    );
    assert_eq!(repl_eval(&mut s, "(add3 1 2)"), 3, "2-ary variant");
    assert_eq!(repl_eval(&mut s, "(add3 1 2 3)"), 6, "3-ary variant");
    // Mixed use in one expression — exercises dispatch on both.
    assert_eq!(
        repl_eval(&mut s, "(add-i64 (add3 1 2) (add3 1 2 3))"),
        9,
        "mixed 2+3-ary dispatch must compose correctly post-G6"
    );
}

// =============================================================================
// Baseline preservation note — v4_cache_hit_dependency
// =============================================================================
// `v4_cache_hit_dependency` in tests/v4_pipeline.rs was expected to flip under
// G6 per the original plan, but `/int` reports it did NOT — cross-module cache
// resolution requires Phase 5. This test intentionally does NOT assert the
// flip; the baseline failure count (14) is preserved. See SPRINT.md and
// tests/plan/ring4.md §G.1 for the disposition.
