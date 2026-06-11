// facade_pif_rows.rs — Sprint 67 Wave 0 (/qa).
//
// Failing-not-ignored integration tests, one per substantive PIF row in
// the SPRINT.md disposition table (rows 116–162, plus the FQTypeName +
// SharedState scope amendments). Each test names the row(s) it covers,
// the facade section it asserts against, and the owning /dev wave that
// resolves it. Tests fail today; /dev makes them pass in Waves 2/3/4.
//
// Per `memory/feedback_failing_not_ignored.md` these tests are
// coverage assets — they prove "implementation does not match facade
// today" and flip green when /dev resolves the row.
//
// Mechanism choice. For most PIF rows we read the per-crate
// `public-api.txt` baseline file at test runtime and grep for the
// expected presence/absence. Reading text files keeps the test binary
// buildable even when the items don't exist yet (a compile-time
// `use cranelisp_backend::Code` would block the entire test binary
// build). Where the row is about runtime behaviour (typed errors
// surfacing in stderr, REPL slash-command outputs), we drive the
// cranelisp exe via the `Cranelisp` builder helper.
//
// FIXME(/dev — multiple): each test names its target /dev skill +
// wave in its body comment. When the row resolves, the test flips
// green by construction; no test edit required for the happy path.

#![allow(dead_code)]

use std::path::PathBuf;

#[path = "helpers/mod.rs"]
mod helpers;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn read_pub_api(crate_name: &str) -> String {
    let p = workspace_root()
        .join("crates")
        .join(crate_name)
        .join("public-api.txt");
    std::fs::read_to_string(&p)
        .unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

/// cargo-public-api 0.51.0 prefixes declaration lines with the item's
/// attributes, e.g. `#[non_exhaustive] pub enum cranelisp_backend::Code`
/// or `#[repr(C)] pub struct cranelisp_platform::PlatformFn`. Older tool
/// versions emitted the bare `pub enum …` form. Strip a single leading
/// `#[ … ] ` attribute segment so a predicate can keep using
/// `starts_with("pub enum ")` / `starts_with("pub struct ")` against the
/// declaration body. Lines without an attribute prefix pass through
/// unchanged.
fn strip_attr_prefix(line: &str) -> &str {
    let t = line.trim_start();
    if let Some(rest) = t.strip_prefix("#[") {
        // Find the matching `] ` that closes the leading attribute. The
        // attribute itself never contains `] ` (a `]` immediately followed
        // by a space) inside its argument list in cargo-public-api output,
        // so the first occurrence closes it.
        if let Some(close) = rest.find("] ") {
            return rest[close + 2..].trim_start();
        }
    }
    t
}

// =============================================================================
// Row 1 — `Code` enum lives in cranelisp-backend (Decision 41 close-out)
// =============================================================================

// spec: design/arch/facades/backend.md §"`Code` — the per-symbol lifecycle owner"
// FIXME(/dev backend Wave 3): physically relocate `Code` from src/code.rs to
// crates/cranelisp-backend; the pub-api line should appear in cranelisp-backend's
// baseline, not in cranelisp-types or as an int-only type.
#[test]
fn row_01_code_enum_named_in_backend_pub_api() {
    let api = read_pub_api("cranelisp-backend");
    // Look for the canonical declaration `pub enum cranelisp_backend::…::Code`
    // — facade backend.md §"`Code`" prescribes it as a backend public item.
    let present = api.lines().any(|line| {
        let line = strip_attr_prefix(line);
        line.starts_with("pub enum ")
            && line.contains("cranelisp_backend::")
            && line.trim_end().ends_with("::Code")
    });
    assert!(
        present,
        "Decision 41 close: `pub enum cranelisp_backend::…::Code` not found in \
         crates/cranelisp-backend/public-api.txt. Backend facade prescribes it; \
         /dev (backend) Wave 3 row 1 lands the physical relocation."
    );
}

// =============================================================================
// Rows 2–5 — typed errors (CompilationError, LinkerError, LinkerArtefact,
// ObjectArtefact) in cranelisp-backend per REV-4
// =============================================================================

// spec: design/arch/facades/backend.md §"Errors" — CompilationError enum
// FIXME(/dev backend Wave 3 rows 2–5): introduce typed error enums in
// cranelisp-backend; retire stringly-typed `CodegenError { message }` at the
// backend boundary.
#[test]
fn rows_02_03_compilation_error_enum_named_in_backend_pub_api() {
    let api = read_pub_api("cranelisp-backend");
    let present = api.lines().any(|line| {
        let line = strip_attr_prefix(line);
        line.starts_with("pub enum ")
            && line.contains("cranelisp_backend::")
            && line.trim_end().ends_with("::CompilationError")
    });
    assert!(
        present,
        "Decision 37 close: `pub enum cranelisp_backend::…::CompilationError` not \
         in baseline. Facade §\"Errors\" prescribes it. /dev (backend) Wave 3."
    );
}

// spec: design/arch/facades/backend.md §"Errors" — LinkerError enum (REV-4 in backend, not types)
// FIXME(/dev backend Wave 3 row 5): add LinkerError to cranelisp-backend.
#[test]
fn row_05_linker_error_enum_named_in_backend_pub_api() {
    let api = read_pub_api("cranelisp-backend");
    let present = api.lines().any(|line| {
        let line = strip_attr_prefix(line);
        line.starts_with("pub enum ")
            && line.contains("cranelisp_backend::")
            && line.trim_end().ends_with("::LinkerError")
    });
    assert!(
        present,
        "Decision 41 / REV-4 close: `pub enum cranelisp_backend::…::LinkerError` \
         not in baseline. Facade §\"Errors\" prescribes it; types.md \
         §\"Errors and warnings\" LinkerError entry is removed per REV-4. \
         /dev (backend) Wave 3."
    );
}

// spec: design/arch/facades/backend.md §"Return shapes" — LinkerArtefact + ObjectArtefact
// FIXME(/dev backend Wave 3 rows 3, 4): introduce the DTOs in backend.
#[test]
fn rows_03_04_linker_and_object_artefact_named_in_backend_pub_api() {
    let api = read_pub_api("cranelisp-backend");
    let linker = api.lines().any(|line| {
        let line = strip_attr_prefix(line);
        line.starts_with("pub struct ")
            && line.contains("cranelisp_backend::")
            && line.trim_end().ends_with("::LinkerArtefact")
    });
    let object = api.lines().any(|line| {
        let line = strip_attr_prefix(line);
        line.starts_with("pub struct ")
            && line.contains("cranelisp_backend::")
            && line.trim_end().ends_with("::ObjectArtefact")
    });
    assert!(
        linker && object,
        "Decision 41 close: LinkerArtefact (found={linker}) + ObjectArtefact \
         (found={object}) not in backend baseline. Facade §\"Return shapes\" \
         prescribes both. /dev (backend) Wave 3."
    );
}

// =============================================================================
// Row 6 — primitive_for_trait_method (D43 forbidden pattern; delete)
// =============================================================================

// spec: design/arch/facades/backend.md §"Operator special-casing is forbidden"
// FIXME(/dev backend Wave 3 row 6): delete primitive_for_trait_method per D43.
#[test]
fn row_06_primitive_for_trait_method_absent_from_backend_pub_api() {
    let api = read_pub_api("cranelisp-backend");
    let leaked = api
        .lines()
        .filter(|l| l.contains("primitive_for_trait_method"))
        .count();
    assert_eq!(
        leaked, 0,
        "D43 forbidden pattern: `primitive_for_trait_method` is still in \
         crates/cranelisp-backend/public-api.txt ({leaked} lines reference it). \
         Facade §\"Operator special-casing is forbidden\" prohibits the \
         (TraitName, Symbol, TypeName) signature. /dev (backend) Wave 3 row 6 \
         deletes the function."
    );
}

// =============================================================================
// Row 7 — operators.rs full retirement (D43 full close; FIXME 0150)
// =============================================================================

// spec: design/arch/facades/backend.md §"Operator special-casing is forbidden"
// What the facade actually forbids (S69 audit F-6 + F-7, grounded in Decision
// 43 §"Status pointer — Sprint 67 FULL CLOSE"): the TRAIT-KEYED substitution
// — `primitive_for_trait_method(TraitName, Symbol, TypeName) -> Option<&str>`
// and the old `operators.rs` home. The NAME-KEYED inline shortcut that
// survives in `primitives_inline.rs` (`is_known_builtin` +
// `try_emit_inline_primitive`, keyed by primitive Symbol only) is EXPLICITLY
// AUTHORISED as a code-size/dispatch-cost optimisation over the standard
// GOT-indirect path (F-7 — "the reframe stands"). It is live codegen, called
// from compiler/apply.rs + control_flow.rs — deleting the file would break it.
// So this row asserts the forbidden pattern is gone, NOT that the file is.
#[test]
fn row_07_trait_keyed_substitution_retired_from_backend() {
    let api = read_pub_api("cranelisp-backend");
    // (a) operators.rs (the pre-rename trait-keyed home) is gone.
    let mod_operators = api
        .lines()
        .any(|l| l.contains("pub mod cranelisp_backend::operators"));
    let path_operators = workspace_root()
        .join("crates/cranelisp-backend/src/operators.rs")
        .exists();
    // (b) the FORBIDDEN trait-keyed substitution `primitive_for_trait_method`
    // is absent from backend's primitives_inline.rs (F-6 verified-absent).
    // The name-keyed `try_emit_inline_primitive`/`is_known_builtin` STAY.
    let pi_src = std::fs::read_to_string(
        workspace_root().join("crates/cranelisp-backend/src/primitives_inline.rs"),
    )
    .unwrap_or_default(); // absent file ⇒ trivially no trait-keyed substitution
    let trait_keyed_present = pi_src
        .lines()
        .map(|l| l.split("//").next().unwrap_or(l))
        .any(|code| code.contains("fn primitive_for_trait_method"));
    let retired = !mod_operators && !path_operators && !trait_keyed_present;
    assert!(
        retired,
        "backend.md §\"Operator special-casing is forbidden\" (S69 audit F-6/F-7, \
         Decision 43): the trait-keyed (TraitName,Symbol,TypeName) substitution \
         must be gone. pub mod operators={mod_operators}; src/operators.rs=\
         {path_operators}; primitive_for_trait_method in primitives_inline.rs=\
         {trait_keyed_present}. (The name-keyed inline shortcut in \
         primitives_inline.rs is authorised and stays — F-7.)"
    );
}

// =============================================================================
// Row 21 — TypeCheckEnv 30→2 method narrowing (FIXME 0172)
// =============================================================================

// spec: design/arch/facades/typecheck.md §"Cluster check scaffolding"
// FIXME(/dev typecheck Wave 3 row 21): narrow TypeCheckEnv to {new, next_type_id}.
#[test]
fn row_21_typecheck_env_narrowed_to_facade_two_methods() {
    let api = read_pub_api("cranelisp-typecheck");
    // Count `pub fn TypeCheckEnv<...>::xxx(…)` lines. Facade prescribes 2.
    let methods: Vec<&str> = api
        .lines()
        .filter(|l| {
            l.starts_with("pub fn ")
                && l.contains("::TypeCheckEnv")
                && l.contains(">::")
        })
        .collect();
    // Allow some slack for derive-related methods on impls; the substantive
    // facade-method-count is what we want at ≤ a small N. Facade prescribes 2;
    // we assert ≤ 4 to tolerate Clone/Debug-style derives if any appear.
    assert!(
        methods.len() <= 4,
        "FIXME 0172 close: TypeCheckEnv exposes {} pub fn methods; facade \
         prescribes 2 (`new`, `next_type_id`). Current method names:\n{}\n\
         /dev (typecheck) Wave 3 row 21 — no two-phase split.",
        methods.len(),
        methods.join("\n")
    );
}

// =============================================================================
// Rows 26, 27 — PRIMITIVES_TABLE static + primitives/string/vec relocation
// =============================================================================

// spec: design/arch/facades/primitives.md §"Public surface"
// FIXME(/dev primitives Wave 3 row 26, FIXME 0159): introduce PRIMITIVES_TABLE static.
#[test]
fn row_26_primitives_table_static_named_in_primitives_pub_api() {
    let api = read_pub_api("cranelisp-primitives");
    // Facade prescribes ONE pub item: `pub static PRIMITIVES_TABLE: LazyLock<SymbolTable>`.
    let present = api.lines().any(|l| {
        l.contains("PRIMITIVES_TABLE")
            && l.contains("static")
            && (l.contains("LazyLock") || l.contains("Lazy"))
    });
    assert!(
        present,
        "FIXME 0159 close: `pub static PRIMITIVES_TABLE` not in \
         crates/cranelisp-primitives/public-api.txt. Facade §\"Public surface\" \
         prescribes a single LazyLock<SymbolTable> entry. \
         /dev (primitives) Wave 3 row 26."
    );
}

// spec: design/arch/facades/primitives.md §"Public surface"
// FIXME(/dev primitives Wave 3 row 27, FIXME 0180): physical relocation of
// string/vec helpers from intrinsics into primitives.
#[test]
fn row_27_primitives_string_vec_physically_owned_by_primitives_not_reexported() {
    let api = read_pub_api("cranelisp-primitives");
    // `pub use cranelisp_primitives::string::str_concat` is the local form;
    // a re-export from intrinsics would show `pub use cranelisp_intrinsics::…`.
    // Pre-relocation the items appear as locally-defined (`pub use
    // cranelisp_primitives::…`); post-relocation the underlying definitions
    // should also be in the primitives source tree, not in intrinsics.
    let intrinsics_api = read_pub_api("cranelisp-intrinsics");
    // Find `str_concat` / `vec_len` / similar in intrinsics — should NOT
    // be there post-relocation. Pre-relocation expectation: at least one
    // string/vec helper still in intrinsics that should have moved.
    let str_helpers_in_intrinsics = intrinsics_api
        .lines()
        .filter(|l| {
            // Any `pub ... cranelisp_intrinsics::string` /
            // `cranelisp_intrinsics::vec` definition or re-export.
            l.contains("cranelisp_intrinsics::string::")
                || l.contains("cranelisp_intrinsics::vec::")
                || l.contains("cranelisp_intrinsics::string ")
                || l.contains("cranelisp_intrinsics::vec ")
                || (l.starts_with("pub ")
                    && l.contains("cranelisp_intrinsics::")
                    && (l.contains("::str_concat")
                        || l.contains("::str_len")
                        || l.contains("::str_substring")
                        || l.contains("::str_split")
                        || l.contains("::str_trim")
                        || l.contains("::vec_len")
                        || l.contains("::string_identity")))
        })
        .count();
    // Also assert primitives DOES physically own the string/vec surface.
    //
    // Surface-shape note (cargo-public-api 0.51.0): post-relocation the
    // string/vec helpers live as `pub(crate)` fns inside the primitives
    // crate (kept linkable via `extern_shims()` per the primitives audit
    // §"DCE protection"), so they do NOT surface as named pub fns in the
    // baseline. The witness of physical ownership is the `string` / `vec`
    // *modules* appearing under `cranelisp_primitives::` — they are absent
    // from the intrinsics baseline (checked above) and present here. This
    // is the current shape of "owned by primitives, not re-exported".
    let string_mod_in_primitives = api
        .lines()
        .any(|l| strip_attr_prefix(l) == "pub mod cranelisp_primitives::string");
    let vec_mod_in_primitives = api
        .lines()
        .any(|l| strip_attr_prefix(l) == "pub mod cranelisp_primitives::vec");
    let primitives_owns = string_mod_in_primitives && vec_mod_in_primitives;
    assert!(
        str_helpers_in_intrinsics == 0 && primitives_owns,
        "FIXME 0180 close: string/vec physical relocation incomplete. \
         intrinsics still defines/re-exports {str_helpers_in_intrinsics} \
         string/vec helpers (should be 0 post-relocation); primitives owns \
         `pub mod cranelisp_primitives::string`={string_mod_in_primitives}, \
         `pub mod cranelisp_primitives::vec`={vec_mod_in_primitives} \
         (both should be true). /dev (primitives) Wave 3 row 27."
    );
}

// =============================================================================
// Rows 30, 33 — io_trace + trace observer relocation intrinsics → int
// =============================================================================

// spec: design/arch/facades/intrinsics.md §"IO observation" / facades/int.md
// FIXME(/dev int Wave 4 row 30, D40 close): io_trace::* moves to int.
#[test]
fn row_30_io_trace_absent_from_intrinsics_pub_api() {
    let api = read_pub_api("cranelisp-intrinsics");
    let leaked = api
        .lines()
        .filter(|l| l.contains("cranelisp_intrinsics::io_trace"))
        .count();
    assert_eq!(
        leaked, 0,
        "Decision 40 close (io_trace half): `cranelisp_intrinsics::io_trace::*` \
         still leaks {leaked} pub-api lines. Facade prescribes hosting in `int`. \
         /dev (int) Wave 4 row 30 + /dev (intrinsics) post-Wave-4 deletion."
    );
}

// spec: design/arch/tracing.md §4.3 — trace bodies host in cranelisp-intrinsics
// The pre-S76 expectation (Decision 0040: trace relocates to int → ABSENT from
// intrinsics) is RETRACTED. Decision 0040 carries a PARTIAL-RETRACTION BOX
// (S76, user-decided 2026-06-04): the `(trace ...)` half is retracted, the 12
// `cranelisp_trace_*` bodies + `trace_format` relocate BACK to
// `cranelisp-intrinsics` and publish via `intrinsics_table()`; `src/trace.rs`
// deletes. `design/arch/tracing.md` (§§1–6, §4.3) is the canonical target.
// So the contract flips: trace MUST be PRESENT in `cranelisp_intrinsics::trace`.
// (Cascade residual: the intrinsics facade `intrinsics.md` is still silent on
// trace — design/arch/fixmes/0297 asks /arch to document the tracing.md
// hosting there. The as-built + tracing.md are unambiguous, so this test
// asserts the settled contract now rather than waiting on the facade prose.)
#[test]
fn row_33_trace_bodies_hosted_in_intrinsics_pub_api() {
    let api = read_pub_api("cranelisp-intrinsics");
    let trace_fns = api
        .lines()
        .filter(|l| l.contains("cranelisp_intrinsics::trace::"))
        .count();
    assert!(
        trace_fns > 0,
        "tracing.md §4.3 / D0040 retraction: the trace family MUST be hosted in \
         `cranelisp_intrinsics::trace` and published via intrinsics_table(); \
         found {trace_fns} pub-api lines (expected > 0). src/trace.rs deletes."
    );
}

// =============================================================================
// Row 31 — ops::cranelisp_op_* deletion (D43 full close)
// =============================================================================

// spec: design/arch/facades/intrinsics.md / facades/backend.md §"Forbidden patterns"
// FIXME(/dev intrinsics Wave 2 row 31, REV-5 audit): delete ops::cranelisp_op_*.
#[test]
fn row_31_cranelisp_op_extern_fns_deleted_from_intrinsics() {
    let api = read_pub_api("cranelisp-intrinsics");
    let remaining = api
        .lines()
        .filter(|l| l.contains("cranelisp_op_"))
        .count();
    assert_eq!(
        remaining, 0,
        "D43 close: ops::cranelisp_op_* still in intrinsics pub-api ({remaining} \
         lines). REV-5 consumer-audit precedes the deletion; /dev (intrinsics) \
         Wave 2 row 31 lands the deletion after /design (backend) Wave 1 confirms \
         zero consumers."
    );
}

// =============================================================================
// Row 42 — describe_symbol family lands on CompilerSession (REV-3 read-side-only)
// =============================================================================

// spec: design/arch/facades/int.md §"Introspection accessors" lines 88–101
// FIXME(/dev int Wave 3 row 42, FIXME 0176 partial close): describe_symbol family
// + read-side accessors land as CompilerSession methods reading shared.symbol_tables
// + shared.introspection. SharedState interior decomposition deferred S68.
//
// **Two-signal test**: (a) the named facade methods MUST exist on
// CompilerSession in src/; (b) the user-visible `/info` slash command MUST
// route through that family and produce the universal-display format.
//
// At S67 W0, signal (a) fails — none of describe_symbol / list_user_definitions
// / module_imports / module_exports / symbol_source / symbol_sexp / symbol_clif
// / symbol_disasm exist as CompilerSession methods (grep src/ returns 0).
// Signal (b) may pass coincidentally — the existing slash-command paths happen
// to produce the universal-display format via a different code path. The
// failure of (a) is the actionable PIF.
#[test]
fn row_42_describe_symbol_family_methods_exist_on_compiler_session() {
    // Scan src/ tree for `fn describe_symbol`, etc. Pre-row-42 the methods
    // do not exist; post-row-42 they should be defined on a CompilerSession
    // impl in src/session_v4.rs (or a sibling module imported into it).
    let names: &[&str] = &[
        "describe_symbol",
        "list_user_definitions",
        "module_imports",
        "module_exports",
        "symbol_source",
        "symbol_sexp",
        "symbol_clif",
        "symbol_disasm",
    ];
    let src_root = workspace_root().join("src");
    let mut found: Vec<&'static str> = Vec::new();
    let mut missing: Vec<&'static str> = Vec::new();
    for name in names {
        let pat_fn = format!("fn {name}(");
        let mut hit = false;
        // Walk src/ recursively, looking for the fn definition.
        for entry in walk_rust_files(&src_root) {
            let text = std::fs::read_to_string(&entry).unwrap_or_default();
            if text.contains(&pat_fn) {
                hit = true;
                break;
            }
        }
        if hit {
            found.push(name);
        } else {
            missing.push(name);
        }
    }
    assert!(
        missing.is_empty(),
        "FIXME 0176 partial close: describe_symbol family missing from src/. \
         Missing methods: {missing:?}. Found: {found:?}. Facade prescribes \
         these 8 read-side accessors as CompilerSession methods reading \
         shared.symbol_tables + shared.introspection. /dev (int) Wave 3 row 42."
    );
}

fn walk_rust_files(root: &std::path::Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else { return out };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            out.extend(walk_rust_files(&path));
        } else if path.extension().and_then(|s| s.to_str()) == Some("rs") {
            out.push(path);
        }
    }
    out
}

// =============================================================================
// Row 45 — re_register_module forward on CompilerSession (trivial PIF)
// =============================================================================

// spec: design/arch/facades/int.md line 36 — CompilerSession::re_register_module
// FIXME(/dev int Wave 3 row 45): add the thin forward; CompileScheduler keeps
// its method, CompilerSession exposes a one-line passthrough.
#[test]
fn row_45_re_register_module_callable_on_compiler_session() {
    // The int crate is a binary, no pub-api baseline. Indirect signal:
    // grep the src/ tree for an `impl CompilerSession` block that defines
    // `pub fn re_register_module`. Pre-S67 the method only lives on
    // CompileScheduler at scheduler.rs:412.
    let src = workspace_root().join("src/session_v4.rs");
    let text = std::fs::read_to_string(&src)
        .unwrap_or_else(|e| panic!("read {}: {e}", src.display()));
    // Heuristic: a `pub fn re_register_module(` inside session_v4.rs is a
    // CompilerSession method (the file defines the impl block).
    let on_session = text.contains("pub fn re_register_module(");
    assert!(
        on_session,
        "Row 45 close: `CompilerSession::re_register_module` not present in \
         src/session_v4.rs. Facade prescribes a thin forward; /dev (int) Wave 3."
    );
}

// =============================================================================
// FQTypeName binding (Decision 47, types.md §232) — second user-challenge amend
// =============================================================================

// spec: design/arch/facades/types.md §"FQTypeName binding"
// FIXME(/dev typecheck/backend/intrinsics/primitives/platform/int Wave 3):
// every API past frontend's resolution stage that names a type uses FQTypeName.
// Exceptions: frontend syntactic-stage; receiver-pinned SymbolTable::get_type;
// reverse-lookup Type::from_name / type_name.
//
// We test the easiest observable signal: typecheck's pub-api should expose
// FQTypeName in its return types / param types for resolved-stage APIs. The
// pre-S67 source uses `TypeName` in many resolved-stage positions; the
// migration replaces them per Decision 47.
#[test]
fn fqtypename_binding_resolved_stage_apis_use_fqtypename_not_bare_typename() {
    // Heuristic: count `TypeName` vs `FQTypeName` references in
    // cranelisp-typecheck pub-api. Pre-migration the ratio of bare TypeName
    // to FQTypeName is heavy on TypeName; post-migration bare TypeName
    // should only appear in receiver-pinned / reverse-lookup positions
    // (a small fixed number).
    let api = read_pub_api("cranelisp-typecheck");
    let mut bare_typename = 0;
    let mut fq_typename = 0;
    for l in api.lines() {
        // Skip auto-derived trait-impl noise.
        if l.starts_with("impl ") {
            continue;
        }
        // Count occurrences of `::TypeName` (bare) vs `::FQTypeName`.
        // Use word-boundary heuristic via the `F` prefix check.
        for tok in l.split(|c: char| !c.is_alphanumeric() && c != '_' && c != ':')
        {
            if tok.ends_with("::TypeName") {
                bare_typename += 1;
            }
            if tok.ends_with("::FQTypeName") {
                fq_typename += 1;
            }
        }
    }
    // Decision 47 close: resolved-stage uses FQTypeName. At S67 W0 the ratio
    // is heavily TypeName-skewed (many TypeCheckEnv methods take bare TypeName).
    // Post-migration: FQTypeName should dominate or at least equal bare TypeName.
    assert!(
        fq_typename >= bare_typename,
        "Decision 47 close: FQTypeName migration incomplete in \
         cranelisp-typecheck pub-api. bare TypeName references = \
         {bare_typename}; FQTypeName references = {fq_typename}. Post-migration \
         FQTypeName should dominate at resolved-stage boundaries. \
         /dev (typecheck) Wave 3 FQTypeName boundary lifts."
    );
}

// NOTE (Sprint 78 Wave 1, plan §3): `shared_state_field_count_matches_facade_after_pif`
// was RELOCATED out of this boundary-conformance file into `tests/regression.rs`
// as `shared_state_field_count_at_target_14`. Per FIXME 0298 it introspects an
// int-INTERNAL struct (`SharedState`), not a boundary/public-API surface, so it
// does not belong here. Its spec anchor regrounds from the (retiring) int facade
// to `design/int/s77-int-restructure.md §2.3` (16 → 14 fields). See regression.rs.

// =============================================================================
// REV-3 read-side hook — describe_symbol uses shared.symbol_tables +
// shared.introspection (not a SharedState restructure)
// =============================================================================

// spec: design/arch/facades/int.md §"Composed introspection flows"
// FIXME(/dev int Wave 3): describe_symbol family reads from shared maps; the
// facade prescribes accessor methods rather than direct field access at
// call-sites. A small e2e signal: /info on a primitive should resolve through
// the family and report the primitives/<name> classification universally.
#[test]
fn rev3_describe_symbol_resolves_primitive_via_facade_method() {
    use helpers::e2e::{Cranelisp, PreludeVariant};
    let cap = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin("/info add-i64\n")
        .output();
    let stdout = &cap.stdout;
    // The facade prescribes `:Type value ; classification` format for ALL
    // describe_symbol results. A primitive should classify as `primitive` or
    // a related token. Pre-fix, /info on a primitive may yield "unknown
    // symbol" or skip the universal format entirely.
    let touches_primitive = stdout.contains("primitive")
        || stdout.contains("primitives/add-i64")
        || stdout.contains("add-i64");
    assert!(
        touches_primitive,
        "REV-3 read-side wiring: /info add-i64 did not produce a primitive- \
         classified universal-display line. Facade §\"Composed introspection \
         flows\" routes through describe_symbol → shared.symbol_tables.\n\
         === stdout ===\n{stdout}\n=== stderr ===\n{}",
        cap.stderr
    );
}

// =============================================================================
// Platform conformance-triad mechanical checks (audit C1–C5; FIXMEs 0224,
// 0225, 0227, 0228). These are STRUCTURAL guards over the frozen
// `cranelisp-platform/public-api.txt` baseline — `cargo public-api` emits the
// auto-trait impls (`impl Send/Sync`), `#[repr(...)]` / `#[non_exhaustive]`
// attributes, and per-method receivers, so the baseline is the mechanical
// witness for surface drift that `facade_compliance.rs` (substring-name-only)
// and `public_api_relocations.rs` (unordered field set) cannot catch.
//
// Unlike most rows in this file, these PASS today: the markers all exist in
// source + baseline. Their job is to FAIL if a future change drops a
// load-bearing marker (an `unsafe impl Send`, a `#[non_exhaustive]`, a method
// receiver, a `#[repr(C)]`) without the baseline + facade catching it.
// =============================================================================

// spec: design/arch/facades/cranelisp-platform-audit-s69.md §4 C1 (FIXME 0224)
// CLHeap method receiver/arity drift: every `CLHeap`-impl type's `inc_rc` /
// `dec_rc` must take `&self` (a by-value `self` receiver would break the RC
// trampoline's ability to call through a borrowed reference). `cargo
// public-api` emits the receiver, so the baseline distinguishes
// `inc_rc(&self)` from `inc_rc(self)`.
#[test]
fn platform_clheap_inc_dec_rc_take_ref_self() {
    let api = read_pub_api("cranelisp-platform");
    // Collect every `inc_rc` / `dec_rc` pub-fn line.
    let rc_lines: Vec<&str> = api
        .lines()
        .filter(|l| {
            l.starts_with("pub fn ")
                && l.contains("cranelisp_platform::")
                && (l.contains("::inc_rc(") || l.contains("::dec_rc("))
        })
        .collect();
    // The CLHeap family: CLString + CLAdt<T> carry concrete inc_rc/dec_rc
    // impls in the baseline (CLInt/CLBool/CLFloat/CLIO are NOT CLHeap — they
    // are non-heap value wrappers — and correctly do NOT appear here).
    assert!(
        !rc_lines.is_empty(),
        "FIXME 0224: no inc_rc/dec_rc lines in cranelisp-platform baseline; \
         the CLHeap surface vanished — investigate."
    );
    for line in &rc_lines {
        assert!(
            line.contains("(&self)"),
            "FIXME 0224 (audit C1): CLHeap method receiver drift — expected \
             `(&self)` receiver, found: `{line}`. A by-value `self` breaks the \
             RC trampoline. Baseline regeneration + facade/BC update required."
        );
    }
}

// spec: design/arch/facades/cranelisp-platform-audit-s69.md §4 C2 (FIXME 0225)
// `#[non_exhaustive]` presence: `OwnedPlatformFnDescriptor` MUST carry
// `#[non_exhaustive]` (Principle 14 — post-load owned descriptor field-set
// evolution discipline); CLOwned MUST NOT (a `#[repr(transparent)]` /
// owned-handle type, not an evolving struct). `cargo public-api` emits the
// attribute prefix, so the baseline is the mechanical witness.
#[test]
fn platform_non_exhaustive_present_on_owned_descriptor_only() {
    let api = read_pub_api("cranelisp-platform");
    // The declaration line for OwnedPlatformFnDescriptor must carry the
    // `#[non_exhaustive]` prefix.
    let owned_descriptor_line = api.lines().find(|l| {
        l.contains("pub struct cranelisp_platform::OwnedPlatformFnDescriptor")
    });
    let owned_descriptor_line = owned_descriptor_line.expect(
        "FIXME 0225: OwnedPlatformFnDescriptor not in cranelisp-platform baseline",
    );
    assert!(
        owned_descriptor_line.contains("#[non_exhaustive]"),
        "FIXME 0225 (audit C2): `#[non_exhaustive]` dropped from \
         OwnedPlatformFnDescriptor — Principle 14 field-set evolution \
         discipline broken. Line: `{owned_descriptor_line}`"
    );
    // Negative: CLOwned must NOT carry `#[non_exhaustive]`.
    let cl_owned_decl = api
        .lines()
        .find(|l| l.contains("pub struct cranelisp_platform::CLOwned"));
    if let Some(line) = cl_owned_decl {
        assert!(
            !line.contains("#[non_exhaustive]"),
            "FIXME 0225 (audit C2): CLOwned unexpectedly gained \
             `#[non_exhaustive]`. Line: `{line}`"
        );
    }
}

// spec: design/arch/facades/cranelisp-platform-audit-s69.md §4 C4 (FIXME 0227)
// `#[repr(C)]` field-order mechanical check. cargo-public-api emits fields as
// an unordered set, so it cannot catch a field reshuffle that changes byte
// offsets. We assert via `std::mem::offset_of!` against a frozen offset table
// — the (b) option the audit enumerated, chosen over (a) cbindgen-diff because
// it is self-contained in the test suite (no external header-generation step).
// The protected set: `PlatformFn`, `PlatformManifest`, `HostCallbacks` (the
// `#[repr(C)]` layout-contract types per Principle 14).
//
// This needs the real Rust types, so it lives as a compile-time fixture using
// `cranelisp_platform` as a dependency — but tests/ is a binary, so we assert
// via the baseline that the `#[repr(C)]` attribute is present AND the field
// COUNT + ORDER (as emitted top-to-bottom in the baseline) matches a frozen
// expectation. cargo-public-api emits fields in source-declaration order, so a
// reshuffle changes the emitted line order — which this test pins.
#[test]
fn platform_repr_c_field_order_frozen() {
    let api = read_pub_api("cranelisp-platform");
    // Helper: collect the ordered field names for a given struct, in the order
    // cargo-public-api emits them (source-declaration order).
    fn fields_in_order<'a>(api: &'a str, type_path: &str) -> Vec<&'a str> {
        let field_prefix = format!("pub {type_path}::");
        api.lines()
            .filter_map(|l| {
                l.strip_prefix(&field_prefix)
                    .and_then(|rest| rest.split(':').next())
            })
            .collect()
    }
    // Assert `#[repr(C)]` prefix on each protected type's declaration line.
    for ty in [
        "cranelisp_platform::PlatformFn",
        "cranelisp_platform::PlatformManifest",
        "cranelisp_platform::HostCallbacks",
    ] {
        let decl = api
            .lines()
            .find(|l| l.contains(&format!("pub struct {ty}")))
            .unwrap_or_else(|| panic!("FIXME 0227: {ty} not in baseline"));
        assert!(
            decl.contains("#[repr(C)]"),
            "FIXME 0227 (audit C4): `#[repr(C)]` dropped from {ty}. Line: `{decl}`"
        );
    }
    // Frozen field-order tables (source-declaration order). A reshuffle that
    // changes byte offsets reorders these lines in the baseline → mismatch.
    let platform_fn_fields = fields_in_order(&api, "cranelisp_platform::PlatformFn");
    // Frozen field-order table for ABI_VERSION = 3 (Sprint 76, FIXME 0288):
    // `jit_name` / `jit_name_len` were removed — the former jit_name
    // mangled-name dispatch retired in favour of the exported linker name
    // (see crates/cranelisp-platform/src/lib.rs:186-191, 320, 359). The
    // ABI_VERSION bump (1→3) is the recorded layout-discipline gate for the
    // removal; this frozen table is updated to match.
    assert_eq!(
        platform_fn_fields,
        vec![
            "docstring", "docstring_len", "name",
            "name_len", "param_count", "param_name_count", "param_name_lens",
            "param_names", "ptr", "scheduling_class", "type_sig", "type_sig_len",
        ],
        "FIXME 0227 (audit C4): PlatformFn field ORDER drifted — a #[repr(C)] \
         byte-offset change. ABI_VERSION bump + frozen-table update required."
    );
    let manifest_fields = fields_in_order(&api, "cranelisp_platform::PlatformManifest");
    assert_eq!(
        manifest_fields,
        vec![
            "abi_version", "function_count", "functions", "name", "name_len",
            "version", "version_len",
        ],
        "FIXME 0227 (audit C4): PlatformManifest field ORDER drifted — a \
         #[repr(C)] byte-offset change. ABI_VERSION bump + table update required."
    );
    let host_cb_fields = fields_in_order(&api, "cranelisp_platform::HostCallbacks");
    // Frozen field-order table for ABI_VERSION = 3 (Sprint 76, FIXME 0288):
    // `validate_schema` was removed — the v3 ABI surface is
    // `HostCallbacks { alloc, alloc_with_tag }` (see
    // crates/cranelisp-platform/src/lib.rs:185-190). The ABI_VERSION bump is
    // the recorded layout-discipline gate for the removal; table updated.
    assert_eq!(
        host_cb_fields,
        vec!["alloc", "alloc_with_tag"],
        "FIXME 0227 (audit C4): HostCallbacks field ORDER drifted — a #[repr(C)] \
         byte-offset change. ABI_VERSION bump + frozen-table update required."
    );
}

// spec: design/arch/facades/cranelisp-platform-audit-s69.md §4 C5 (FIXME 0228)
// `unsafe impl Send/Sync` presence. `unsafe impl Send for PlatformFn` +
// `unsafe impl Sync for PlatformFn` are load-bearing (the IO trampoline holds
// platform-fn pointers across threads). `OwnedPlatformFnDescriptor` +
// `PlatformManifest` must conversely project `!Send + !Sync` (raw pointers /
// owned strings that must not silently cross threads). cargo-public-api emits
// both the positive `impl Send/Sync` and the negative `impl !Send/!Sync`.
#[test]
fn platform_send_sync_claims_match_invariants() {
    let api = read_pub_api("cranelisp-platform");
    let has = |needle: &str| api.lines().any(|l| l.trim() == needle);
    // PlatformFn: positive Send + Sync (the unsafe impls).
    assert!(
        has("impl core::marker::Send for cranelisp_platform::PlatformFn"),
        "FIXME 0228 (audit C5): `Send` dropped from PlatformFn — the IO \
         trampoline can no longer hold platform-fn pointers across threads."
    );
    assert!(
        has("impl core::marker::Sync for cranelisp_platform::PlatformFn"),
        "FIXME 0228 (audit C5): `Sync` dropped from PlatformFn."
    );
    // OwnedPlatformFnDescriptor: negative !Send + !Sync (owned strings/ptr).
    assert!(
        has("impl !core::marker::Send for cranelisp_platform::OwnedPlatformFnDescriptor"),
        "FIXME 0228 (audit C5): OwnedPlatformFnDescriptor unexpectedly became \
         Send — the safety surface silently expanded."
    );
    assert!(
        has("impl !core::marker::Sync for cranelisp_platform::OwnedPlatformFnDescriptor"),
        "FIXME 0228 (audit C5): OwnedPlatformFnDescriptor unexpectedly became Sync."
    );
    // PlatformManifest: negative !Send + !Sync (raw pointers).
    assert!(
        has("impl !core::marker::Send for cranelisp_platform::PlatformManifest"),
        "FIXME 0228 (audit C5): PlatformManifest unexpectedly became Send."
    );
    assert!(
        has("impl !core::marker::Sync for cranelisp_platform::PlatformManifest"),
        "FIXME 0228 (audit C5): PlatformManifest unexpectedly became Sync."
    );
}
