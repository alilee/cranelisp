// golden_clif_w0b.rs — the W0.b totalization shippability gate.
//
// PURPOSE (design/arch/backend-keyed-consumer.md §4 W0.b + §5). W0 delivered the
// producer carriers WRITE-ONLY; the W0.b flip (next wave) makes typecheck the
// SOLE mono-view producer for every codegen-reached body — including the
// LENIENT/synthetic entry classes that legitimately fail strict
// `MonoExpr::from_expr` — and turns the backend's `lenient_mono_from_expr` arm
// into a hard error. W0.b's stated shippability gate is **CLIF byte-identity**:
// a passing suite does NOT prove the generated code is unchanged, only that it
// still runs. This harness captures the CURRENT (pre-W0.b) CLIF for the lenient
// classes as the golden, so the W0.b flip can be ASSERTED to lower identically.
//
// GATE. This file IS the named W0.b acceptance gate. The `/dev` W0.b wave runs
//   cargo nextest run --test golden_clif_w0b
// as its acceptance: GREEN means the typecheck-built lenient view lowers
// byte-identically to the deleted backend-built one; a RED frame names the
// lenient class whose codegen drifted. If W0.b is genuinely emission-affecting
// for a class (it must not be — the wave is behaviour-invariant), the golden is
// re-baselined SCOPED + attributed per MANIFEST.md, never wholesale.
//
// LENIENT ENTRY CLASSES (design §5 finding 1; backend lib.rs:654-657 rustdoc).
// The lenient arm is taken when a codegen-reached entry has `codegen_view: None`
// OR its kind is not `UserFn{Concrete}` (`requires_codegen_view == false`). Six
// classes reach it; FIVE are live-reachable by a free-standing program and are
// pinned here:
//   01 ctor `Def` synthetic body            (user::Box.MkBox)
//   02 synthesised field accessor           (user::Point.x / user::Point.y)
//   03 `f$Var` multi-sig variant body       (user::pick$Int / user::pick$Int+Int)
//   04 `__expr` §3.11.2-disposition-3 body  (user::__expr)
//   05 non-concretized macro-clause body    (user::__macro_twice_clause_0)
// The SIXTH — "generic template reached by direct compile" — is structurally
// NOT live-reachable: pure `Polymorphic`/`Constrained` templates are excluded
// from the codegen name-set (`src/worker.rs:896-902`) and produce no `.o`
// (`nice_worker.rs:171`); the only path that lowers a bare template is the
// backend-crate unit helper `jit.rs::compile_defn`, which has NO live caller
// (design §5 finding 3; verified by call-site grep 2026-07-15). Since `tests/`
// is e2e-only (two tiers, no middle), that class CANNOT be an e2e golden — its
// byte-identity guard is the backend unit suite (KC-W0-6). See MANIFEST.md
// §"Class 06".
//
// NORMALIZATION (the /testing call). Frames are compared BYTE-VERBATIM, NO
// canonicalization — the L-B1 precedent (tests/fixtures/clif_baseline/MANIFEST.md
// §Capture contract): SSA value numbers, block labels, GOT-slot operands, and
// wrapper identity are LOAD-BEARING for this gate (masking them would blind it
// to the exact carrier-vs-code drift W0.b must not introduce). Byte-identity is
// admissible because the dump IS deterministic — each capture double-runs the
// binary and asserts the two dumps are identical BEFORE comparing to the golden.
// A benign renumber is therefore not a risk to accept a mask for; if a future
// codegen change ever makes a class nondeterministic, THAT is the signal to
// investigate (a real ordering bug), not to canonicalize.
//
// MECHANISM. `CRANELISP_CODEGEN_DUMP='*'` (the framed `; === CLIF module::symbol
// ===` dump, stderr), cold-cache `--run --no-cache` (each symbol dumps exactly
// ONCE — the JIT pass; the nice-worker `.o` cache-write pass is structurally
// eliminated, so a DUPLICATE FRAME is a hard error, never deduped), emission-
// affecting env unset (kept in lockstep with the L-B1 smoke's env_remove pin
// list — a THIRD consumer of this extraction is the bar to unify the three).
//
// spec: design/arch/backend-keyed-consumer.md §4 W0.b — CLIF byte-identity gate
// plan: tests/plan/PLAN.md §S110 KC-W0-2

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::Cranelisp;

/// Capture the sorted, byte-verbatim CLIF frame set for a corpus entry via one
/// cold-cache `--run --no-cache` under `CRANELISP_CODEGEN_DUMP='*'`.
///
/// Extraction mirrors `tests/ownership_fences.rs::clif_golden_single_module_smoke`
/// and `tests/scripts/clif_golden.sh dump()` (review F6: keep the sites in
/// lockstep; the bar to unify is a third consumer — this IS that third consumer,
/// but unification is a `/dev`+`/qa` tooling change out of this gate's scope).
fn capture_frames(corpus_rel: &str) -> String {
    let corpus = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/clif_w0b/corpus")
            .join(corpus_rel),
    )
    .unwrap_or_else(|e| panic!("W0.b corpus fixture {corpus_rel} unreadable: {e}"));

    let out = Cranelisp::new()
        .run("user.cl")
        .user(&corpus)
        .cli_flag("--no-cache")
        .env("CRANELISP_CODEGEN_DUMP", "*")
        // Emission-affecting pins (MANIFEST §Capture contract; kept in sync with
        // the L-B1 smoke). Each gates CLIF emission (heap.rs / sparkability.rs)
        // or reshapes the pre-typecheck bind chain (NO_IO_SCHEDULE); the trace
        // vars write to stderr — the dump channel — so they are cleared too.
        .env_remove("CRANELISP_NO_OWNERSHIP")
        .env_remove("CRANELISP_NO_LENIENT")
        .env_remove("CRANELISP_CAPTURE_BORROW")
        .env_remove("CRANELISP_NONATOMIC_RC")
        .env_remove("CRANELISP_RC_STATS")
        .env_remove("CRANELISP_RC_DEC_CHECK")
        .env_remove("CRANELISP_NO_IO_SCHEDULE")
        .env_remove("CRANELISP_RC_TRACE")
        .env_remove("CRANELISP_CODEGEN_TRACE")
        .env_remove("CRANELISP_GOT_TRACE")
        .env_remove("CRANELISP_MODULE_TRACE")
        .env_remove("CRANELISP_SCHEDULER_TRACE")
        .env_remove("CRANELISP_IO_TRACE")
        .output();

    extract_sorted_frames(&out.stderr)
}

/// Extract `; === CLIF <name> === ... ; === end CLIF <name> ===` frames from a
/// dump stream, sorted by `module::symbol`, byte-verbatim. A duplicate frame
/// (cache-pass leak) and zero frames (empty-vs-empty false green) are both hard
/// errors — the S102 review F3/F4 classes.
fn extract_sorted_frames(stderr: &str) -> String {
    let re =
        regex::Regex::new(r"(?s); === CLIF (\S+) ===\n.*?; === end CLIF (\S+) ===\n").unwrap();
    let mut frames: std::collections::BTreeMap<String, String> = Default::default();
    for cap in re.captures_iter(stderr) {
        assert_eq!(
            &cap[1], &cap[2],
            "malformed CLIF frame: start/end symbol names disagree (interleaved \
             or truncated dump); stderr:\n{stderr}"
        );
        let prev = frames.insert(cap[1].to_string(), cap[0].to_string());
        assert!(
            prev.is_none(),
            "DUPLICATE FRAME: {} — under --no-cache each symbol dumps exactly \
             once (JIT pass); a second frame means the nice-worker .o cache-write \
             pass leaked into the capture (config drift). Hard error — do NOT \
             dedup.",
            &cap[1]
        );
    }
    let dumped: String = frames.into_values().collect();
    assert!(
        !dumped.is_empty(),
        "no CLIF frames captured from CRANELISP_CODEGEN_DUMP — the empty-vs-empty \
         false-green class (S102 Wave 1); stderr:\n{stderr}"
    );
    dumped
}

/// The gate body: double-capture (determinism self-test — the normalization
/// admissibility precondition), then byte-compare against the committed golden.
fn assert_golden_clif(entry: &str) {
    let corpus_rel = format!("{entry}.cl");
    let golden_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/clif_w0b/golden")
        .join(format!("{entry}.clif"));
    let golden = std::fs::read_to_string(&golden_path).unwrap_or_else(|e| {
        panic!(
            "W0.b golden missing at {} ({e}) — capture it via the corpus fixture \
             per tests/fixtures/clif_w0b/MANIFEST.md §Capture contract",
            golden_path.display()
        )
    });

    // Determinism self-test: two independent captures must be byte-identical
    // BEFORE trusting a golden compare. This is what makes strict byte-identity
    // (no canonicalization) admissible — a nondeterministic dump would be a real
    // ordering bug to investigate, never a reason to mask.
    let a = capture_frames(&corpus_rel);
    let b = capture_frames(&corpus_rel);
    assert_eq!(
        a, b,
        "NONDETERMINISTIC W0.b capture for {entry}: two captures of the same \
         corpus diverged. The byte-identity gate rests on determinism — a diff \
         here is a real ordering/scheduling bug in codegen, not a masking case."
    );

    assert_eq!(
        a, golden,
        "W0.b lenient-class '{entry}' CLIF diverged from its golden. Under W0.b \
         the typecheck-built lenient view MUST lower byte-identically to the \
         backend-built one (design/arch/backend-keyed-consumer.md §4 W0.b). If \
         this change-set is genuinely emission-affecting, re-baseline SCOPED + \
         attributed per tests/fixtures/clif_w0b/MANIFEST.md — never wholesale."
    );
}

// =============================================================================
// The five live-reachable lenient classes.
// =============================================================================

// spec: design/arch/backend-keyed-consumer.md §5 finding 1 — ctor `Def` lenient
// synthetic body (`DefKind::Constructor`, requires_codegen_view == false).
#[test]
fn golden_clif_w0b_ctor_def() {
    assert_golden_clif("01_ctor_def");
}

// spec: design/arch/backend-keyed-consumer.md §5 finding 1 — synthesised field
// accessor lenient body (`Concrete{slot}` with `codegen_view: None`).
#[test]
fn golden_clif_w0b_synth_accessor() {
    assert_golden_clif("02_synth_accessor");
}

// spec: design/arch/backend-keyed-consumer.md §5 finding 1 — `f$Var` multi-sig
// variant lenient body (backend lib.rs multi-sig `_ => lenient_mono_from_expr`).
#[test]
fn golden_clif_w0b_multisig_variant() {
    assert_golden_clif("03_multisig_variant");
}

// spec: design/arch/backend-keyed-consumer.md §5 finding 1 — `__expr`
// (§3.11.2 disposition-3) lenient body (requires_codegen_view == false).
#[test]
fn golden_clif_w0b_expr_disposition3() {
    assert_golden_clif("04_expr_disposition3");
}

// spec: design/arch/backend-keyed-consumer.md §5 finding 1 — non-concretized
// macro-clause lenient body (no typecheck view; macros expand pre-typecheck).
#[test]
fn golden_clif_w0b_macro_clause() {
    assert_golden_clif("05_macro_clause");
}
