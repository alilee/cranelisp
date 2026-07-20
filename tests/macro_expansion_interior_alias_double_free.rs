// macro_expansion_interior_alias_double_free.rs — FIXME 0638 repro pin (S113 W1).
//
// A deterministic memory-safety defect on the MACRO-CLAUSE JIT invocation path.
// After 0614 (S111) moved derive's helpers to a dependency module, a macro whose
// body calls a dependency-module helper that returns a DEEP INTERIOR ALIAS (an
// interior tail of its argument), then allocates over it (an `smap`), DOUBLE-FREES
// at invocation:
//
//   (count-ctors (deftype Color Red Green Blue))
//   => panic at crates/cranelisp-intrinsics/src/alloc.rs:222 "double free …"
//      (SIGSEGV plain; "match failed" under RC_TRACE — symptom-polymorphic heap
//      corruption).
//
// The IDENTICAL helper logic works via a plain cross-module FUNCTION call in
// `--run` (correct result) — the fault is SPECIFIC to the macro-expansion
// invocation path (JIT-invoked macro clause + Sexp marshalling) combined with a
// helper that matches its argument multiple times and returns a deep interior
// alias (`dt-body` returns `rest`, an interior tail of `dt`, while `dt` is also
// matched by `dt-has-docstring`).
//
// ATTRIBUTION (PLAN §I.4, re-checked at HEAD post-CS-5): a DISTINCT defect — NOT
// cured by CS-5, NOT §3.7, NOT 0633 — on the macro-clause JIT invocation path
// (`src/expander.rs` invoke core + `src/marshal.rs` Sexp marshalling; intrinsics
// alloc adjacent). Owner /dev (int marshal/invoke seam first).
//
// CORRECT RESULT: `count-ctors` counts the three constructors (Red/Green/Blue) →
// the macro expands to the integer 3 → `main` returns `(Pure 3)` → exit 3. The
// pin asserts exit 3 and no double-free/panic; today it corrupts → RED.
//
// Modules are stdlib-free: `primitives` + the synthetic `macros` module (Sexp
// constructors + `SNil`/`SCons`) + two tiny local modules. The `(import [prelude
// []])` line in the preserved verbatim files is vestigial (imports no names) and
// dropped for test isolation (root CLAUDE.md §Design Principles — Stdlib
// separation); all other content is verbatim from FIXME 0638.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// dthelp.cl — helper module. `dt-body` returns `rest`, an interior tail alias of
// `dt`; `dt-has-docstring` also matches `dt`. Verbatim (minus the vestigial
// `(import [prelude []])`).
const DTHELP: &str = "\
(import [primitives [add-i64 sub-i64 eq-i64]])
(import [macros [*]])

(defn sfold [f init xs]
  (match xs [SNil init (SCons h t) (sfold f (f init h) t)]))
(defn sreverse [xs] (sfold (fn [acc x] (SCons x acc)) SNil xs))
(defn smap [f xs] (sreverse (sfold (fn [acc x] (SCons (f x) acc)) SNil xs)))
(defn sdrop [n xs]
  (if (eq-i64 n 0) xs
    (match xs [SNil SNil (SCons _ t) (sdrop (sub-i64 n 1) t)])))

(defn dt-head [dt]
  (match dt
    [(SexpList items)
     (match items [(SCons _ tail1) (match tail1 [(SCons head _) head _ (SexpSym \"e\")]) _ (SexpSym \"e\")])
     _ (SexpSym \"e\")]))
(defn dt-has-docstring [dt]
  (let [third (sdrop 2 (match dt [(SexpList items) items _ SNil]))]
    (match third [(SCons elem _) (match elem [(SexpStr _) true _ false]) _ false])))
(defn dt-name [dt]
  (let [head (dt-head dt)]
    (match head [(SexpSym s) s (SexpList items) (match items [(SCons first _) (match first [(SexpSym s) s _ \"e\"]) _ \"e\"]) _ \"e\"])))
(defn dt-body [dt]
  (match dt
    [(SexpList items)
     (match items
       [(SCons _ tail1)
        (match tail1 [(SCons _ rest) (if (dt-has-docstring dt) (match rest [(SCons _ ctors) ctors _ SNil]) rest) _ SNil])
        _ SNil])
     _ SNil]))
(defn dt-constructors [dt]
  (let [body (dt-body dt)]
    (match body
      [(SCons first _)
       (match first [(SexpBracket _) (SCons (SexpList (SCons (SexpSym (dt-name dt)) body)) SNil) _ body])
       _ SNil])))

(defn slen [xs] (sfold (fn [acc _] (add-i64 acc 1)) 0 xs))
";

// mac.cl — macro whose body returns the interior alias then allocates over it.
const MAC: &str = "\
(import [primitives [add-i64]])
(import [macros [*]])
(import [dthelp [dt-constructors smap slen]])

(defmacro count-ctors [dt]
  (SexpInt (slen (smap (fn [x] x) (dt-constructors dt)))))
";

// usemac.cl — `--run` this → double-free at alloc.rs:222 (correct answer: exit 3).
const USEMAC: &str = "\
(import [primitives [Pure]])
(import [mac [count-ctors]])

(defn main []
  (Pure (count-ctors (deftype Color Red Green Blue))))
";

fn build(mode: &str) -> helpers::e2e::CrOutput {
    let b = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .file("dthelp.cl", DTHELP)
        .file("mac.cl", MAC)
        .file("usemac.cl", USEMAC);
    let b = match mode {
        "run" => b.run("usemac.cl"),
        "link" => b.link_then_run("usemac.cl"),
        _ => unreachable!(),
    };
    b.output()
}

fn assert_no_corruption(out: &helpers::e2e::CrOutput, mode: &str) {
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("double free")
            && !c.contains("invalid free")
            && !c.to_lowercase().contains("panicked")
            && !c.contains("match failed"),
        "[{mode}] the macro-clause interior-alias invocation MUST NOT corrupt the \
         heap (double-free / SIGSEGV / `match failed`); got:\n{c}"
    );
    out_assert_exit(out, 3, mode, &c);
}

fn out_assert_exit(out: &helpers::e2e::CrOutput, code: i32, mode: &str, c: &str) {
    assert_eq!(
        out.status.code(),
        Some(code),
        "[{mode}] `count-ctors (deftype Color Red Green Blue)` counts 3 \
         constructors → `main` returns `(Pure 3)` → exit 3; got exit {:?}:\n{c}",
        out.status.code()
    );
}

// --run face.
// spec: spec/09-macros.md §9.2 — a macro clause invoked at expansion time computes
// over its Sexp argument; the result MUST be memory-safe regardless of interior
// aliasing in helper returns.
// defect: class=uaf locus=src macro-clause invoke/marshal seam (src/expander.rs + src/marshal.rs; intrinsics alloc adjacent) found=S111 owner=/dev
#[test]
fn macro_clause_interior_alias_double_free_run() {
    let out = build("run");
    assert_no_corruption(&out, "run");
}

// MODE-AXIS twin (R-1, /qa reconciliation §2.2) — the M1-OFF (default allocator,
// no quarantine) DOUBLE-FREE-ASSERT face, made explicit under `RC_DEC_CHECK` so the
// double-free surfaces as an RC-underflow assert rather than a bare glibc abort.
// A defect's observability must not depend on lane config: with M1 (quarantine) ON
// the double-free is neutralized into an M3-leak parity abort (a quarantined block
// cannot be re-freed-into-reuse), so enabling quarantine by default would silently
// reclassify this defect's face. This OFF twin pins the double-free-assert face so
// a partial fix cannot green one face while the other still fires. RED-until-fixed.
//
// NOTE — the paired M1-ON (quarantine → M3-leak parity abort) twin rides the
// diagnostic-mode landing in this window: the quarantine env var is NOT yet present
// (no `CRANELISP_*` quarantine/scrub/parity toggle exists at HEAD), so the M1-ON
// cell cannot be authored against a real interface yet — it lands with the mode
// infrastructure it depends on.
// spec: spec/09-macros.md §9.2 — macro-clause invocation is memory-safe (M1-OFF face).
// defect: class=uaf locus=src macro-clause invoke/marshal seam (src/expander.rs + src/marshal.rs; intrinsics alloc adjacent) found=S111 owner=/dev
#[test]
fn macro_clause_interior_alias_double_free_m1_off_assert_face() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .env("CRANELISP_RC_DEC_CHECK", "1")
        .file("dthelp.cl", DTHELP)
        .file("mac.cl", MAC)
        .file("usemac.cl", USEMAC)
        .run("usemac.cl")
        .output();
    assert_no_corruption(&out, "run/M1-OFF/RC_DEC_CHECK");
}

// MODE-AXIS twin (R-1) — the M1-ON (quarantine) face. Under
// `CRANELISP_QUARANTINE_FREED` the freed block is withheld (is_live stays false),
// so the second free is DETERMINISTICALLY DETECTED (exit 134 "double free or
// invalid free") at the faulting op — vs the perturbation-sensitive "match failed"
// under M1-OFF. RED-until-fixed: the spec-correct contract is exit 3, abort-free.
//
// FINDING (W5b probe, /qa R-1 premise correction): R-1 predicted M1 → an M3-leak
// PARITY-abort face (a quarantined block "neutralized into a leak"). The observed
// M1 face is instead a DETERMINISTIC double-free DETECTION (the intrinsics dealloc
// double-free check fires against the never-live-again quarantined block, exit 134
// "double free"), NOT a silent leak reaching the atexit parity check. The mode-
// AXIS point of R-1 still holds — the defect's observability is config-dependent
// (M1-OFF perturbation vs M1-ON deterministic abort), so both faces need a cell —
// but the M1-ON face is a double-free-detection abort, not an M3-leak. Reported.
// spec: spec/09-macros.md §9.2 — macro-clause invocation is memory-safe (M1-ON face).
// defect: class=uaf locus=src macro-clause invoke/marshal seam (src/expander.rs + src/marshal.rs; intrinsics alloc adjacent) found=S111 owner=/dev
#[test]
fn macro_clause_interior_alias_double_free_m1_on_quarantine_face() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::None)
        .env("CRANELISP_QUARANTINE_FREED", "1")
        .file("dthelp.cl", DTHELP)
        .file("mac.cl", MAC)
        .file("usemac.cl", USEMAC)
        .run("usemac.cl")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() == Some(3)
            && !c.contains("double free")
            && !c.contains("invalid free"),
        "[M1-ON/quarantine] the macro-clause interior-alias invocation MUST run to \
         exit 3 abort-free even with quarantine ON; today the withheld block's \
         second free is deterministically detected (exit 134 'double free'); got \
         exit {:?}:\n{c}",
        out.status.code()
    );
}

// MS-P6 M1-double-free capability fence — RETIRED S114 (was the W5/0638
// flip-hazard, `sprints/SPRINT.md` §Notes; the pattern FIXME 0690 sanctions:
// re-plant on a synthetic fault OR retire with rationale).
//
// This e2e fence proved M1 (quarantine) makes a double-free deterministically
// detected — but it could ONLY exist while a real double-free DEFECT was open:
// it rode the LIVE 0638 macro-clause double-free as its planted fault. The W5
// 0638 fix (deep marshal protect-on-build) closed that fault, so under
// `CRANELISP_QUARANTINE_FREED` the program now runs clean to exit 3 (fenced GREEN
// by `macro_clause_interior_alias_double_free_m1_on_quarantine_face` above) and
// this capability cell inverted to RED.
//
// It CANNOT be re-planted this sprint: every listed free-class double-free
// (0638, 0641, 0633) is fixed, and the only remaining open free-class defect —
// MS-P7 / cow-set (`safety_oracle_lane.rs`) — is (a) W7-scheduled, so planting on
// it re-creates the exact in-sprint flip-hazard this cleanup removes, and
// (b) a reuse-corruption UAF, NOT a genuine second-`dealloc`: under quarantine it
// runs clean to exit 9 in `--run` AND `--link` (measured S114), so it never
// triggers M1's "double free" abort. Well-typed source cannot double-free, so no
// synthetic plant survives quarantine as a detectable second-free.
//
// The DURABLE M1 double-free verification is the `/dev`(intrinsics) unit seam
// (design/intrinsics/diagnostic-modes.md §6 MS-P6: "the e2e face is the oracle
// lane" — it only demonstrates against an open defect; the mechanism is unit-
// pinned): `crates/cranelisp-intrinsics/src/alloc/tests.rs::test_double_free_detected`
// (direct double-`dealloc` → "double free" panic) +
// `.../diagnostics/tests.rs::{quarantine_withholds_all_blocks_without_cap,
// parity_report_flags_double_free}`. Escalated to /qa for the standing MS-P6
// e2e-face disposition — reinstate this fence if a new open double-free defect
// gives it a live fault to catch.

// --link face — same defect through the linked binary.
// spec: spec/09-macros.md §9.2 — macro-clause invocation is memory-safe in all modes.
// defect: class=uaf locus=src macro-clause invoke/marshal seam (src/expander.rs + src/marshal.rs; intrinsics alloc adjacent) found=S111 owner=/dev
#[test]
fn macro_clause_interior_alias_double_free_link() {
    let out = build("link");
    assert_no_corruption(&out, "link");
}

// REPL face — `(count-ctors (deftype Color Red Green Blue))` evaluates to
// `:primitives/Int 3`. The FIXME records "REPL also corrupts."
// spec: spec/09-macros.md §9.2 — macro-clause invocation is memory-safe in the REPL.
// defect: class=uaf locus=src macro-clause invoke/marshal seam (src/expander.rs + src/marshal.rs; intrinsics alloc adjacent) found=S111 owner=/dev
#[test]
fn macro_clause_interior_alias_double_free_repl() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .file("dthelp.cl", DTHELP)
        .file("mac.cl", MAC)
        .stdin("(import [mac [count-ctors]])\n(count-ctors (deftype Color Red Green Blue))\n")
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("double free")
            && !c.contains("invalid free")
            && !c.to_lowercase().contains("panicked")
            && !c.contains("match failed"),
        "[repl] the macro-clause interior-alias invocation MUST NOT corrupt the \
         heap; got:\n{c}"
    );
    assert!(
        c.contains(":primitives/Int 3"),
        "[repl] `(count-ctors (deftype Color Red Green Blue))` MUST evaluate to 3 \
         constructors → `:primitives/Int 3`; got:\n{c}"
    );
}
