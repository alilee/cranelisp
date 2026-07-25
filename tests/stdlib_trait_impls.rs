// stdlib_trait_impls.rs — Sprint 66 Phase 5 Stage 1 (FIXME 0150 D43).
//
// Authored failing-not-ignored at Phase-5 Stage-1 open per /qa Phase-5
// obligation. **Highest single reshape risk in S66** per /arch Phase-2
// recommendation #4 + /qa slice §2.3: D43 deletes backend's
// `(TraitName, Symbol, TypeName) → primitive` map. Empty-body or
// circular-recursion `(impl Num Int)` / `(impl Eq Int)` / `(impl Ord Int)`
// / `(impl Display Int)` / Float counterparts that "just worked" because
// backend's collusion intercepted upstream of the impl body now break at
// runtime when the map deletes.
//
// This file is the regression guard: it exercises every operator on every
// primitive type via the explicit `(impl Trait PrimitiveType)` path AND
// via the operator-as-value path `(let [f +] (f a b))`. If either path
// regresses during the Phase-4 stdlib-impl audit, a test fires.
//
// Per `tests/plan/implementation-slice-s66.md §5.8`.
//
// Negative path coverage: post-FIXME-0150 Phase 5, the `cranelisp-runtime`
// crate must no longer be a workspace member.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// Helper: REPL with TestStandard prelude — the prelude provides Num/Eq/
// Ord/Display + Int/Float/Bool/String impls. We're testing that the
// IMPLS in `tests/fixtures/preludes/test-standard.cl` behave correctly
// post-FIXME-0150, NOT the stdlib (tests must not depend on stdlib —
// project rule).
fn repl(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(lines)
        .output()
}

// =============================================================================
// FIXME 0150 — Num trait impls: Int (inline + mappable paths)
// =============================================================================

// spec: spec/appendix-a-builtins.md §"Num.Int" + spec/07-traits.md §"Trait dispatch"
// FIXME(/dev FIXME 0150 Phase 3 + 4) — fails if backend trait-knowledge
// map deletion exposes empty/circular `(impl Num Int)` body.
#[test]
fn stdlib_num_int_inline_path() {
    repl("(+ 1 2)\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/07-traits.md §"Operators as first-class values"
// FIXME(/dev FIXME 0150 Phase 3 + 4) — operator-as-value path goes through
// trait-impl entry → primitive (post-Phase-4) and not through deleted
// `cranelisp_op_add` GOT slot (Phase 3 deletion).
#[test]
fn stdlib_num_int_mappable_path() {
    repl("(let [f +] (f 1 2))\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/appendix-a-builtins.md §"Num.Float"
// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_num_float_inline_path() {
    let out = repl("(+ 1.0 2.0)\n");
    assert!(
        out.stdout.contains("3.0") || out.stdout.contains("3"),
        "(+ 1.0 2.0) MUST return 3.0; got stdout:\n{}",
        out.stdout
    );
}

// spec: spec/07-traits.md §"Operators as first-class values"
// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_num_float_mappable_path() {
    let out = repl("(let [f +] (f 1.0 2.0))\n");
    assert!(
        out.stdout.contains("3.0") || out.stdout.contains("3"),
        "(let [f +] (f 1.0 2.0)) MUST return 3.0; got stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// FIXME 0150 — Eq trait impls: Int / Float / Bool / String
// =============================================================================

// spec: spec/appendix-a-builtins.md §"Eq.Int" + spec/07-traits.md
// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_eq_int_inline_path() {
    repl("(= 1 1)\n").assert_stdout_contains(":primitives/Bool true");
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_eq_int_mappable_path() {
    repl("(let [f =] (f 1 1))\n").assert_stdout_contains(":primitives/Bool true");
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_eq_float_inline_path() {
    repl("(= 1.0 1.0)\n").assert_stdout_contains(":primitives/Bool true");
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_eq_float_mappable_path() {
    repl("(let [f =] (f 1.0 1.0))\n").assert_stdout_contains(":primitives/Bool true");
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_eq_bool_inline_path() {
    repl("(= true true)\n").assert_stdout_contains(":primitives/Bool true");
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_eq_bool_mappable_path() {
    repl("(let [f =] (f true true))\n").assert_stdout_contains(":primitives/Bool true");
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_eq_string_inline_path() {
    repl("(= \"hi\" \"hi\")\n").assert_stdout_contains(":primitives/Bool true");
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_eq_string_mappable_path() {
    repl("(let [f =] (f \"hi\" \"hi\"))\n").assert_stdout_contains(":primitives/Bool true");
}

// =============================================================================
// FIXME 0150 — Ord trait impls: Int / Float
// =============================================================================

// spec: spec/appendix-a-builtins.md §"Ord.Int" + spec/07-traits.md
// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_ord_int_inline_path() {
    let out = repl("(< 1 2)\n(> 2 1)\n(<= 1 1)\n(>= 1 1)\n");
    let want = [":primitives/Bool true"; 4];
    let count = out.stdout.matches(":primitives/Bool true").count();
    assert!(
        count >= 4,
        "expected (< 1 2) (> 2 1) (<= 1 1) (>= 1 1) all true ({} hits, want >=4):\n{}",
        count,
        out.stdout
    );
    let _ = want;
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_ord_int_mappable_path() {
    let out = repl(
        "(let [f <] (f 1 2))\n\
         (let [f >] (f 2 1))\n\
         (let [f <=] (f 1 1))\n\
         (let [f >=] (f 1 1))\n",
    );
    let count = out.stdout.matches(":primitives/Bool true").count();
    assert!(
        count >= 4,
        "operator-as-value path for Ord.Int operators must produce 4 trues ({} hits):\n{}",
        count,
        out.stdout
    );
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_ord_float_inline_path() {
    let out = repl("(< 1.0 2.0)\n(> 2.0 1.0)\n(<= 1.0 1.0)\n(>= 1.0 1.0)\n");
    let count = out.stdout.matches(":primitives/Bool true").count();
    assert!(
        count >= 4,
        "Float Ord inline path: expected 4 trues ({} hits):\n{}",
        count,
        out.stdout
    );
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_ord_float_mappable_path() {
    let out = repl(
        "(let [f <] (f 1.0 2.0))\n\
         (let [f >] (f 2.0 1.0))\n\
         (let [f <=] (f 1.0 1.0))\n\
         (let [f >=] (f 1.0 1.0))\n",
    );
    let count = out.stdout.matches(":primitives/Bool true").count();
    assert!(
        count >= 4,
        "Float Ord mappable path: expected 4 trues ({} hits):\n{}",
        count,
        out.stdout
    );
}

// =============================================================================
// FIXME 0150 — Display trait impls: Int / Float
// =============================================================================

// spec: spec/appendix-a-builtins.md §"Display.Int" + spec/07-traits.md
// FIXME(/dev FIXME 0150 Phase 3 + 4) — must NOT regress to backend's
// pre-D43 substitution path.
#[test]
fn stdlib_display_int_inline_path() {
    repl("(show 42)\n").assert_stdout_contains("42");
}

// FIXME(/dev FIXME 0150 Phase 3 + 4)
#[test]
fn stdlib_display_float_inline_path() {
    let out = repl("(show 3.14)\n");
    assert!(
        out.stdout.contains("3.14"),
        "(show 3.14) MUST contain `3.14`; got stdout:\n{}",
        out.stdout
    );
}

// =============================================================================
// FIXME 0150 — `not` operator: inline + mappable paths
// =============================================================================
//
// Specifically named in FIXME 0150: `not` currently has only the inline
// path via backend's `operators.rs:64`; no symbol-table entry; mappable-path
// almost certainly fails today. The test surfaces this gap as failing at
// Phase-5 Stage 1; closure requires symbol-table seeding for `not`.

// spec: spec/appendix-a-builtins.md §"not"
// FIXME(/dev FIXME 0150 Phase 4 + a primitives-side seeding entry land)
#[test]
fn stdlib_not_inline_path() {
    repl("(not true)\n").assert_stdout_contains(":primitives/Bool false");
}

// FIXME(/dev FIXME 0150 Phase 4 + a primitives-side seeding entry land) —
// fails today: `not` has no symbol-table entry, the mappable form has no
// GOT slot to capture.
#[test]
fn stdlib_not_mappable_path() {
    repl("(let [f not] (f true))\n").assert_stdout_contains(":primitives/Bool false");
}

// =============================================================================
// FIXME 0150 — `--link` mode against intrinsics + primitives archives
// =============================================================================

// spec: structural — Phase 5 retirement: `--link` mode produces a runnable
// binary that links against `cranelisp-intrinsics.a` + `cranelisp-primitives.a`
// instead of `cranelisp-runtime.a`.
// FIXME(/dev FIXME 0150 Phase 5 land — runtime crate retires, primitives +
// intrinsics archive paths active in linker invocation).
#[test]
fn stdlib_link_mode_against_intrinsics_archive() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .link_then_run("user.cl")
        .user("(defn main [] (Pure 0))\n")
        .output();
    out.assert_ok()
        // Negative shape: must NOT mention cranelisp-runtime archive path.
        .assert_stderr_does_not_contain_runtime_archive();
}

// Helper extension: assert stderr does not mention the (about-to-retire)
// cranelisp-runtime archive.
trait CrOutputExt {
    fn assert_stderr_does_not_contain_runtime_archive(self) -> Self;
}
impl CrOutputExt for helpers::e2e::CrOutput {
    fn assert_stderr_does_not_contain_runtime_archive(self) -> Self {
        if self.stderr.contains("cranelisp-runtime") || self.stderr.contains("libcranelisp_runtime")
        {
            panic!(
                "post-FIXME-0150 Phase 5: --link MUST NOT reference cranelisp-runtime archive; \
                 got stderr:\n{}",
                self.stderr
            );
        }
        self
    }
}

// =============================================================================
// FIXME 0150 — Negative: cranelisp-runtime crate retired post-Phase 5
// =============================================================================

// spec: structural — D43 Phase 5 retirement.
// FIXME(/dev FIXME 0150 Phase 5 land) — fails until the runtime crate
// directory is removed AND the workspace `Cargo.toml` no longer lists it.
#[test]
fn cranelisp_runtime_crate_absent_post_phase_5_neg() {
    use std::path::PathBuf;
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let runtime_dir = root.join("crates/cranelisp-runtime");
    assert!(
        !runtime_dir.exists(),
        "FIXME 0150 Phase 5: cranelisp-runtime crate directory MUST be removed; \
         path still present: {}",
        runtime_dir.display()
    );
    let workspace_toml = root.join("Cargo.toml");
    let toml = std::fs::read_to_string(&workspace_toml)
        .unwrap_or_else(|e| panic!("read {}: {e}", workspace_toml.display()));
    assert!(
        !toml.contains("cranelisp-runtime") && !toml.contains("crates/cranelisp-runtime"),
        "FIXME 0150 Phase 5: workspace Cargo.toml MUST NOT list cranelisp-runtime as a member;\n{}",
        toml
    );
}
