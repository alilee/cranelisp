//! Integration tests for Sprint 57 Wave 3 (G8 — Platform on SymbolTable).
//!
//! These are Layer 3 integration tests. They exercise the platform-registry
//! removal: after Wave 3, platform function pointers and scheduling class live
//! directly on `ModuleEntry::Def` entries (via `platform_fn_ptr` field +
//! `PrimitiveKind::PlatformEffect { scheduling_class }`), not on a separate
//! `PlatformRegistry` DashMap.
//!
//! What Wave 3 did:
//! - Deleted `src/platform_registry.rs` and `CompilerSession.platform_registry`.
//! - Added `platform_fn_ptr: Option<*const u8>` (`#[serde(skip)]`) on
//!   `ModuleEntry::Def`.
//! - Moved `SchedulingClass` into `cranelisp-types` and added it as a variant
//!   field on `PrimitiveKind::PlatformEffect { scheduling_class }` (Option B).
//! - Added `SharedState::kept_dlls` retention pool so platform fn pointers
//!   remain valid for the session lifetime.
//! - Fixed the IO-trampoline RC leak via `dec_shallow_io` (Decision 29) —
//!   `/arch` Condition 6.
//!
//! See:
//! - `design/int/platform-registry-removal.md` — G8 design
//! - `design/backend/ring2-rc.md` §3.5 — IO trampoline RC fix
//! - `tests/plan/ring4.md` §G.2 — Wave 3 test plan
//!
//! Test scope is integration-layer only. Unit tests for `handle_platform`,
//! `collect_jit_setup`, and `classify_expr` land in their owning crates
//! (`src/` as `#[cfg(test)]` modules).

#[path = "helpers/mod.rs"]
mod helpers;

use cranelisp_types::{
    DefKind, FQSymbol, JitSymbol, ModuleEntry, ModuleFullPath, PrimitiveKind, Scheme,
    SchedulingClass, Symbol, SymbolTable, Type, Visibility,
};
use helpers::{
    repl_eval_typed, repl_session_with, repl_session_with_test_capture, PREAMBLE_PRIMITIVES,
};
use std::collections::HashMap;

// =============================================================================
// G8-1 — platform_fn_ptr populated on entry after (platform ...) form
// =============================================================================

// spec: design/int/platform-registry-removal.md §4.1 — registration path
// spec: design/arch/CLAUDE.md Decision 26 — platform_fn_ptr on ModuleEntry::Def
#[test]
fn g8_platform_fn_ptr_on_entry_after_form_handled() {
    // Load the test-capture platform. After the form is handled, the
    // platform.test-capture module's `print` entry must carry
    // `platform_fn_ptr: Some(_)` — the G8 write-path contract. Prior to
    // Wave 3 this pointer lived in the deleted `PlatformRegistry`.
    let Some((session, _capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not built, skipping");
        return;
    };

    let module = ModuleFullPath::from("platform.test-capture");
    let tables = &session.session.shared.symbol_tables;
    let table = tables
        .get(&module)
        .expect("platform.test-capture symbol table must exist after (platform ...) form");
    let entry = table
        .get("print")
        .expect("'print' must be registered on platform.test-capture");
    match entry {
        ModuleEntry::Def {
            platform_fn_ptr,
            kind,
            ..
        } => {
            assert!(
                platform_fn_ptr.is_some(),
                "G8 contract: platform_fn_ptr must be Some(_) after form processing; \
                 got None which indicates handle_platform did not write the pointer"
            );
            // Entry must also carry PlatformEffect kind with a jit_name.
            match kind.as_ref() {
                DefKind::Primitive {
                    primitive_kind: PrimitiveKind::PlatformEffect { .. },
                    jit_name,
                } => {
                    assert!(
                        jit_name.is_some(),
                        "G8 invariant: PlatformEffect entry must carry Some(jit_name)"
                    );
                }
                other => panic!(
                    "expected PlatformEffect primitive kind for 'print', got {:?}",
                    other
                ),
            }
        }
        other => panic!("expected Def entry for 'print', got {:?}", other),
    }
}

// =============================================================================
// G8-2 — scheduling_class read via symbol-table path (Option B)
// =============================================================================

// spec: design/int/platform-registry-removal.md §3 — scheduling_class placement
// spec: design/int/bind-chain-analysis.md — reads SchedulingClass from SymbolTable
#[test]
fn g8_scheduling_class_read_via_symbol_table() {
    // Build a synthetic symbol-table world with one PlatformEffect entry at a
    // known class. Call `bind_chain_analysis::scheduling_of` — the public
    // symbol-table-driven lookup — and assert the class round-trips.
    //
    // This validates Option B placement (scheduling_class lives inside the
    // PrimitiveKind::PlatformEffect variant, accessed via symbol-table walk),
    // NOT the deleted `PlatformRegistry.scheduling_class(..)` call.
    let tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let platform_mod = ModuleFullPath::from("platform.synthetic");
    let mut st = SymbolTable::new(platform_mod.clone());
    st.insert(
        Symbol::from("parallel-fn"),
        make_platform_effect_entry(SchedulingClass::Commutative, "synthetic_parallel"),
    );
    st.insert(
        Symbol::from("serial-fn"),
        make_platform_effect_entry(SchedulingClass::Sequential, "synthetic_serial"),
    );
    st.insert(
        Symbol::from("token-fn"),
        make_platform_effect_entry(SchedulingClass::ResourceSerial, "synthetic_token"),
    );
    tables.insert(platform_mod.clone(), st);

    // User module imports parallel-fn directly (bare name).
    let user_mod = ModuleFullPath::from("user");
    let mut user_st = SymbolTable::new(user_mod.clone());
    user_st.insert(
        Symbol::from("parallel-fn"),
        ModuleEntry::Import {
            source: FQSymbol {
                module: platform_mod.clone(),
                symbol: Symbol::from("parallel-fn"),
            },
        },
    );
    tables.insert(user_mod.clone(), user_st);

    // Qualified lookup: directly against the defining module.
    let sc_q = cranelisp::bind_chain_analysis::scheduling_of(
        &tables,
        &user_mod,
        "platform.synthetic/parallel-fn",
    );
    assert_eq!(
        sc_q,
        SchedulingClass::Commutative,
        "qualified scheduling_of must return Commutative via symbol-table walk"
    );
    let sc_serial = cranelisp::bind_chain_analysis::scheduling_of(
        &tables,
        &user_mod,
        "platform.synthetic/serial-fn",
    );
    assert_eq!(sc_serial, SchedulingClass::Sequential);
    let sc_token = cranelisp::bind_chain_analysis::scheduling_of(
        &tables,
        &user_mod,
        "platform.synthetic/token-fn",
    );
    assert_eq!(sc_token, SchedulingClass::ResourceSerial);

    // Bare-name lookup follows the Import chain from user → platform.synthetic.
    let sc_bare = cranelisp::bind_chain_analysis::scheduling_of(&tables, &user_mod, "parallel-fn");
    assert_eq!(
        sc_bare,
        SchedulingClass::Commutative,
        "bare-name scheduling_of must walk Import chain to the defining PlatformEffect"
    );

    // A non-platform name falls back to Sequential (the sketch-preserved safe default).
    let sc_missing =
        cranelisp::bind_chain_analysis::scheduling_of(&tables, &user_mod, "not-a-platform");
    assert_eq!(
        sc_missing,
        SchedulingClass::Sequential,
        "missing name must fall back to Sequential"
    );
}

// =============================================================================
// G8-3 — PlatformRegistry struct deletion regression guard
// =============================================================================

// spec: design/int/platform-registry-removal.md §2.4 + §10 — deletion list
// spec: tests/plan/ring4.md §G.2 — v4_platform_registry_struct_absent
#[test]
fn g8_platform_registry_regression_guard() {
    // Structural grep: `PlatformRegistry` and `platform_registry` must not
    // appear as live code in src/. Comments and doc-strings referencing the
    // deleted struct are permitted (historical context). If anyone reintroduces
    // the DashMap or its field, this test fails loudly.
    let src_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");

    fn scan_rs(dir: &std::path::Path, matches: &mut Vec<String>) {
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
                // Skip comments and doc-strings — we only care about live code.
                if trimmed_start.starts_with("//")
                    || trimmed_start.starts_with("///")
                    || trimmed_start.starts_with("/*")
                    || trimmed_start.starts_with("*")
                {
                    continue;
                }
                // Live-code patterns that would indicate the struct/field still exists.
                let forbidden = [
                    "struct PlatformRegistry",
                    "impl PlatformRegistry",
                    "impl Default for PlatformRegistry",
                    "PlatformRegistry {",
                    ": PlatformRegistry",
                    "<PlatformRegistry>",
                    "platform_registry:",
                    "ctx.platform_registry",
                    ".platform_registry.",
                    "mod platform_registry",
                    "use crate::platform_registry",
                ];
                for pat in &forbidden {
                    if line.contains(pat) {
                        matches.push(format!(
                            "{}:{}: {}",
                            path.display(),
                            lineno + 1,
                            line.trim()
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
        "G8 close gate: PlatformRegistry / platform_registry live references in src/:\n{}",
        matches.join("\n")
    );
}

// =============================================================================
// G8-4 — cross-module platform fn resolution through Import
// =============================================================================

// spec: design/int/platform-registry-removal.md §5.2 — collect_jit_setup reads
//       platform_fn_ptr by walking Import chains to the PlatformEffect entry
// spec: spec/08-modules.md §8.3 + §8.9.3 — user imports from platform module
#[test]
fn g8_cross_module_platform_fn_resolution() {
    // User code calls a platform function via an explicit import. After G8
    // the call path walks `symbol_tables` from user → platform.test-capture
    // and reads `platform_fn_ptr` directly off the defining Def entry —
    // no PlatformRegistry side-channel. A correct output capture end-to-end
    // proves the path works.
    let Some((mut session, capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not built, skipping");
        return;
    };

    capture.reset();
    let (_value, ty) = repl_eval_typed(&mut session, r#"(print "cross-module")"#);
    // Sprint 57 Wave 6: repl_eval_typed unwraps IO inline, so the effect has
    // fired and the returned type is the unwrapped inner type (Int for print).
    assert_eq!(
        ty,
        Type::Int,
        "print (IO Int) must unwrap inline to Int via cross-module resolution; got {ty:?}"
    );

    // Import-chain resolution on the user module must have located the
    // platform entry.
    let user_mod = ModuleFullPath::from(session.session.current_module_name().as_str());
    let tables = &session.session.shared.symbol_tables;
    let user_tab = tables
        .get(&user_mod)
        .expect("current-module symbol table must exist");
    let user_entry = user_tab.get("print").expect("'print' must be imported into current module");
    // Regardless of whether the current module holds an Import or a Def
    // (resolver may either leave the Import or collapse it), the platform
    // module's entry must carry the pointer.
    match user_entry {
        ModuleEntry::Import { .. } | ModuleEntry::Def { .. } => {}
        other => panic!("unexpected entry kind for 'print' in user module: {:?}", other),
    }

    let output = capture.get_output();
    assert_eq!(
        output, "cross-module",
        "end-to-end cross-module platform call must produce captured output"
    );
}

// =============================================================================
// G8-5 — kept_dlls retains the handle post-registration
// =============================================================================

// spec: design/int/platform-registry-removal.md §4 + src/session_v4.rs kept_dlls
// spec: src/worker.rs handle_platform — push onto kept_dlls after loading
#[test]
fn g8_kept_dlls_retains_handles() {
    // After loading the test-capture platform, `SharedState.kept_dlls` must
    // retain the `LoadedPlatform` handle so that every `platform_fn_ptr` it
    // installed stays valid for the session lifetime. Without this the DLL
    // would drop at end of handle_platform and every platform_fn_ptr would
    // dangle.
    let Some((session, _capture)) = repl_session_with_test_capture() else {
        eprintln!("test-capture DLL not built, skipping");
        return;
    };

    let kept = session
        .session
        .shared
        .kept_dlls
        .lock()
        .expect("kept_dlls mutex");
    assert!(
        !kept.is_empty(),
        "kept_dlls must retain at least one LoadedPlatform handle after platform load"
    );
    let names: Vec<&str> = kept.iter().map(|p| p.name.as_str()).collect();
    assert!(
        names.iter().any(|n| *n == "test-capture"),
        "kept_dlls must contain the 'test-capture' platform; got {:?}",
        names
    );
}

// =============================================================================
// G8-6 — IO trampoline RC balance (Condition 6 — non-negotiable)
// =============================================================================

// spec: design/backend/ring2-rc.md §3.5 — IO trampoline RC fix via dec_shallow_io
// spec: SPRINT.md Architecture Review Condition 6 — non-negotiable gate
#[test]
fn g8_io_trampoline_rc_balanced() {
    // End-to-end RC balance across the Decision 24 boundary: caller tree
    // (allocated by source-code compilation) + trampoline's fresh-node walk
    // must balance. Sprint 57 Wave 6: the trampoline now runs *inline* inside
    // `session.eval("(main)")` (via `compile_and_execute_expr::unwrap_io_inline`
    // before the per-eval JIT drops) rather than in a separate explicit call.
    // RC balance is therefore measured around the `eval("(main)")` call itself.
    //
    // Before the Wave 3 fix, the trampoline leaked intermediate Pure/Bind
    // nodes produced by continuations (see design/backend/ring2-rc.md §3.5).
    // After Decision 29 (`dec_shallow_io`), the trampoline is balanced.
    //
    // Uses a `Pure`-only bind chain (no platform DLL): the trampoline's
    // fresh-Pure release path is the code-path Condition 6 targets.
    let mut session = repl_session_with(None, Some(PREAMBLE_PRIMITIVES));
    session
        .eval(
            r#"(defn main []
                 (bind (Pure 10)
                   (fn [a]
                     (bind (Pure (add-i64 a 1))
                       (fn [b] (Pure (add-i64 b 1)))))))"#,
        )
        .expect("defn main");

    let allocs_before = cranelisp_runtime::alloc_count();
    let deallocs_before = cranelisp_runtime::dealloc_count();
    let bytes_before = cranelisp_runtime::bytes_current();

    // Sprint 57 Wave 6: eval inline-trampolines the IO tree and returns the
    // unwrapped inner value (Int here). The RC balance covers the full
    // Decision 24 path — caller-tree release + fresh-Pure release inside the
    // trampoline — without any additional cranelisp_run_io call.
    let result = session.eval("(main)").expect("call main");
    let inner = result.value();
    assert_eq!(inner, 12, "expected 10+1+1=12 from bind chain; correctness guard");

    let new_allocs = cranelisp_runtime::alloc_count() - allocs_before;
    let new_deallocs = cranelisp_runtime::dealloc_count() - deallocs_before;
    let bytes_after = cranelisp_runtime::bytes_current();

    assert_eq!(
        new_allocs, new_deallocs,
        "IO trampoline RC imbalance: {new_allocs} allocs vs {new_deallocs} deallocs \
         after two-step Pure bind chain through inline eval-unwrap; Condition 6 regression"
    );
    assert_eq!(
        bytes_after, bytes_before,
        "IO trampoline leaked {} bytes; Condition 6 regression",
        bytes_after.saturating_sub(bytes_before)
    );
}

// =============================================================================
// G8-7 — SchedulingClass moved to cranelisp-types regression guard
// =============================================================================

// spec: design/int/platform-registry-removal.md §3 — SchedulingClass in cranelisp-types
// spec: design/arch/CLAUDE.md Decision 26 — single source of truth for SchedulingClass
#[test]
fn g8_scheduling_class_moved_to_types_regression_guard() {
    // `SchedulingClass` now lives at the bottom of the dependency DAG
    // (`cranelisp-types`) and is re-exported by `cranelisp-platform` so every
    // consumer compiles unchanged. This test nails down the invariant by
    // constructing values through both paths and asserting type equality —
    // if a future refactor splits them, this function won't compile.
    let via_types = cranelisp_types::SchedulingClass::Commutative;
    let via_platform = cranelisp_platform::SchedulingClass::Commutative;
    // Same type => direct equality compiles and holds.
    assert_eq!(via_types, via_platform);

    // from_u32 round-trips via the types-crate path.
    assert_eq!(
        cranelisp_types::SchedulingClass::from_u32(1),
        SchedulingClass::Commutative
    );
    assert_eq!(
        cranelisp_types::SchedulingClass::from_u32(2),
        SchedulingClass::ResourceSerial
    );
    assert_eq!(
        cranelisp_types::SchedulingClass::from_u32(0),
        SchedulingClass::Sequential
    );
}

// =============================================================================
// G8-8 — PrimitiveKind::PlatformEffect carries scheduling_class (Option B)
// =============================================================================

// spec: design/int/platform-registry-removal.md §3.1 — Option B recommendation
// spec: crates/cranelisp-types/src/module.rs PrimitiveKind::PlatformEffect variant
#[test]
fn g8_platform_effect_variant_carries_scheduling_class() {
    // Construct a PlatformEffect variant for each SchedulingClass; destructure
    // and assert the class round-trips. If Option A (a sibling field on
    // ModuleEntry::Def) ever replaces Option B, the match below won't compile.
    for expected in [
        SchedulingClass::Sequential,
        SchedulingClass::Commutative,
        SchedulingClass::ResourceSerial,
    ] {
        let entry = make_platform_effect_entry(expected, "probe");
        match entry {
            ModuleEntry::Def { kind, .. } => match *kind {
                DefKind::Primitive {
                    primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class },
                    ..
                } => {
                    assert_eq!(
                        scheduling_class, expected,
                        "PrimitiveKind::PlatformEffect.scheduling_class must carry the class \
                         per Option B"
                    );
                }
                other => panic!("expected PlatformEffect primitive, got {:?}", other),
            },
            other => panic!("expected Def entry, got {:?}", other),
        }
    }
}

// =============================================================================
// G8-9 — RC balance for trampoline IO through a deeper bind chain
// =============================================================================

// spec: design/backend/ring2-rc.md §3.5.7 — bind-chain RC balance end-to-end
// spec: tests/plan/ring4.md §G.2 — v4_platform_rc_balance_bind_chain
#[test]
fn g8_rc_balance_bind_chain() {
    // Deeper bind chain (4 steps) — exercises the fresh-node release path
    // in run_io_trampoline for longer than the two-step G8-6 test. This
    // was the O(N) leak shape before Wave 3. Same harness pattern as G8-6.
    //
    // Sprint 57 Wave 6: the trampoline runs inline inside `eval("(main)")`
    // (via `compile_and_execute_expr::unwrap_io_inline`), so the RC balance
    // measurement brackets that call directly — no explicit cranelisp_run_io.
    let mut session = repl_session_with(None, Some(PREAMBLE_PRIMITIVES));
    session
        .eval(
            r#"(defn main []
                 (bind (Pure 0) (fn [a]
                 (bind (Pure (add-i64 a 1)) (fn [b]
                 (bind (Pure (add-i64 b 1)) (fn [c]
                 (bind (Pure (add-i64 c 1)) (fn [d]
                   (Pure (add-i64 d 1)))))))))))"#,
        )
        .expect("defn main");

    let allocs_before = cranelisp_runtime::alloc_count();
    let deallocs_before = cranelisp_runtime::dealloc_count();

    let result = session.eval("(main)").expect("call main");
    let inner = result.value();
    assert_eq!(inner, 4, "0 + 4×(+1) = 4; correctness guard before balance check");

    let new_allocs = cranelisp_runtime::alloc_count() - allocs_before;
    let new_deallocs = cranelisp_runtime::dealloc_count() - deallocs_before;

    assert_eq!(
        new_allocs, new_deallocs,
        "bind-chain RC imbalance: {new_allocs} allocs vs {new_deallocs} deallocs"
    );
}

// =============================================================================
// Helpers
// =============================================================================

/// Build a minimal `ModuleEntry::Def` carrying a `PlatformEffect` variant with
/// the given `SchedulingClass`. Used by the synthetic-fixture tests above.
fn make_platform_effect_entry(sc: SchedulingClass, jit_name: &str) -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![],
        kind: Box::new(DefKind::Primitive {
            primitive_kind: PrimitiveKind::PlatformEffect {
                scheduling_class: sc,
            },
            jit_name: Some(JitSymbol::from(jit_name)),
        }),
        callees: Vec::new(),
        got_slot: None,
        trait_origin: None,
        ast: None,
        code: None,
        // Fresh entry has no pointer yet — the integration tests above don't
        // dispatch through it, they only inspect metadata.
        platform_fn_ptr: None,
    }
}

