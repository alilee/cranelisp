// zeroable_return_dispatch_nonpty.rs — S112 W6, /qa ruling 7 (leg-(c) adjacent).
//
// The `/repl` W5 close FLAGGED a NON-DETERMINISTIC failure of the Zeroable
// section of `repl/demos/05-traits.demo` (lines 46–63) under PTY replay — it
// failed identically on HEAD pre-edit, had no minimal repro, and was
// inconsistent between runs (suspected PTY playback artifact). Ruling 7:
// reproduce NON-PTY FIRST (an unreduced nondeterministic symptom attributed by
// guess is the named layered-bug trap), before any compiler attribution.
//
// This test extracts that Zeroable section into a piped-stdin (NON-PTY) e2e and
// drives it 25× fresh. The section is return-type-dispatch (Zeroable) — the
// same machinery as the W6 leg-(c) cross-mode probe (spec_07_traits.rs AG-4).
//
// OUTCOME (verified 2026-07-18, /testing): 25/25 (and 10/10 of the FULL demo
// through the real stdlib prelude) produce BYTE-IDENTICAL, GREEN output non-PTY
// — fully deterministic. Per ruling 7(ii) the PTY non-determinism is therefore
// NOT a compiler defect; attribution moves to the PTY replay harness itself
// (owner /repl, playback artifact), recorded there — NOT as a compiler defect.
// This e2e stands as the GREEN regression guard: if the Zeroable section ever
// becomes non-deterministic (or leaks) NON-PTY, this test names it as a real
// compiler defect. NOT a `// defect:` repro (no compiler defect is asserted).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// The Zeroable section of 05-traits.demo (lines 46–63), reduced to the language
// forms (the demo's comment/section-header lines carry no output). Return-type
// dispatch: `(deftrait Zeroable (zed [] self))` — the dispatch position is the
// RETURN type. Bare `zed` self-documents; `(zed)` is unresolvable (clean
// §3.11); `:Int (zed)` / `:Float (zed)` pin the return type and dispatch.
const ZEROABLE_SECTION: &str = "(deftrait Zeroable (zed [] self))\n\
     (impl Zeroable Int (defn zed [] 0))\n\
     (impl Zeroable Float (defn zed [] 0.0))\n\
     zed\n\
     (zed)\n\
     :Int (zed)\n\
     :Float (zed)\n";

const RUNS: usize = 25;

// spec: spec/07-traits.md §7.4 — return-type-polymorphic dispatch (Zeroable
// `zed`) is DETERMINISTIC and clean when driven non-PTY. `:Int (zed)` → 0,
// `:Float (zed)` → 0.0, a bare `(zed)` is a clean §3.11 ambiguity, and no run
// leaks a backend error. Driven 25× fresh, every run MUST produce identical,
// green output — proving the PTY-replay non-determinism (ruling 7) is a
// playback artifact, not a compiler defect.
#[test]
fn zeroable_section_deterministic_and_clean_across_25_nonpty_runs() {
    let mut signatures: Vec<String> = Vec::with_capacity(RUNS);

    for i in 0..RUNS {
        let out = Cranelisp::new()
            .repl()
            .with_prelude(PreludeVariant::PrimitivesOnly)
            .stdin(ZEROABLE_SECTION)
            .output();
        let combined = format!("{}{}", out.stdout, out.stderr);

        // Per-run correctness: dispatch to both impls + the clean ambiguity.
        assert!(
            combined.contains(":primitives/Int 0"),
            "run {i}: `:Int (zed)` MUST dispatch to the Int impl → 0; got:\n{combined}"
        );
        assert!(
            combined.contains(":primitives/Float 0.0"),
            "run {i}: `:Float (zed)` MUST dispatch to the Float impl → 0.0; got:\n{combined}"
        );
        assert!(
            combined.contains("ambiguous type"),
            "run {i}: a bare `(zed)` MUST be a clean §3.11 return-type ambiguity; \
             got:\n{combined}"
        );
        // No run may leak a backend/runtime failure.
        for leak in ["undefined function", "codegen error", "panic", "<invalid"] {
            assert!(
                !combined.contains(leak),
                "run {i}: the Zeroable section MUST NOT leak `{leak}` non-PTY; \
                 got:\n{combined}"
            );
        }

        // Reduce to a determinism signature: the value/error lines in order.
        let sig: String = combined
            .lines()
            .filter_map(|l| {
                if let Some(idx) = l.find(":primitives/") {
                    Some(l[idx..].trim().to_string())
                } else if l.contains("ambiguous type") {
                    Some("ambiguous type".to_string())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("|");
        signatures.push(sig);
    }

    // Determinism: every one of the 25 runs MUST share the same signature.
    let first = &signatures[0];
    let all_equal = signatures.iter().all(|s| s == first);
    assert!(
        all_equal,
        "the Zeroable section MUST be DETERMINISTIC across {RUNS} non-PTY runs \
         (ruling 7: non-PTY reproduction FIRST). Distinct signatures observed:\n{:#?}",
        {
            let mut uniq: Vec<&String> = signatures.iter().collect();
            uniq.sort();
            uniq.dedup();
            uniq
        }
    );
}
