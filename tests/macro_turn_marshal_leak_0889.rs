// macro_turn_marshal_leak_0889.rs — the regression fence on a KNOWN, ACCEPTED,
// EXACTLY-QUANTIFIED leak.
//
// FIXME 0889 (`design/arch/fixmes/0889-recover-the-macro-turn-marshal-leak.md`).
// Every macro expansion leaks at the int-side macro-turn marshal boundary:
//
//   - marshalled argument trees are never RC-decremented (`src/marshal.rs`
//     states this as intent in its own header; each cell further pinned by the
//     FIXME-0638 `protect_marshalled_cell` +1);
//   - the expansion-result tree is never consumed after `runtime_to_sexp`
//     copies it (`src/expander.rs::invoke_clause` drops the `i64`).
//
// Closed form, exact on every S118 probe point:
//
//     residual per expansion
//         = |marshalled arg cells + args spine| + |non-aliased result cells|
//
// The full stdlib prelude sums to exactly **1143** allocations per session. It
// is COMPILE-TIME bounded and does not grow with runtime execution (the plan's
// P1/P2 probes are 0), which is why it is acceptable to carry — and why it is
// nonetheless a leak that must be recovered, not accounted around
// (`sprints/SPRINT.md` §Notes 2026-07-26, user decision).
//
// ===========================================================================
// WHY THESE CELLS ARE PINNED GREEN AT A NON-ZERO NUMBER.
//
// This is the unusual case where the right fence asserts the defect's EXACT
// present magnitude rather than the correct value. The alternative — a failing
// cell asserting zero — records that the leak exists but nothing about its
// size, so a partial fix, a silent doubling, or a change of shape all leave it
// equally and uninformatively RED.
//
// Pinned at the documented values, ANY movement flips these cells: a partial
// fix, a regression that widens the residual, or the real 0889 fix that takes
// it to zero. Whoever moves the number is forced to come here and update the
// record — which is the point, because `0889`'s closed-form model and the
// prelude's 1143 are quoted in the plan, the FIXME, and four retrofitted
// baseline cells, and a stale model there is worse than no model.
//
// **A GREEN here is not a claim that the behaviour is correct.** It is a claim
// that the behaviour is exactly what the record says it is. When 0889 lands,
// both cells fail on their `expected 2, measured 0` / `expected 1, measured 0`
// message; the fixing change-set flips both `assert_residual` values to `0`,
// renames nothing, and the cells become ordinary balance guards on the
// macro-turn boundary for good.
// ===========================================================================
//
// MEASUREMENT DISCIPLINE. Both cells use the `helpers::marginal` harness, so the
// number asserted is a DIFFERENCE between two children that differ in exactly
// one macro invocation — not an absolute count. The library trees are identical
// but for a single call site; the program, prelude module set, env, binary and
// `--no-cache` invocation are the same on both sides. This is what makes "+2"
// mean "two cells per expansion of this shape" rather than "two cells more than
// whatever this build happened to allocate".
//
// THE TWO SHAPES, and why these two:
//
//   | shape                              | predicted by the model      | measured |
//   |------------------------------------|-----------------------------|---------:|
//   | one expansion, one marshalled arg  | 1 arg cell + 1 args spine   |       +2 |
//   | one expansion, nullary, no quote   | 0 args + 1 result cell      |       +1 |
//
// They are the model's two independent terms, isolated: the nullary shape has
// no marshalled arguments at all, so its +1 is the RESULT term alone; the
// one-arg shape's +2 is the ARGUMENT term (`SexpInt` + `SCons` spine) with a
// result that aliases its argument and therefore contributes nothing. Together
// they pin both halves of the closed form, so a fix that addresses only one
// half is visible as one cell flipping and the other holding.
//
// Armed `CRANELISP_ALLOC_PARITY=1` fingerprints from the Branch-F probe
// (recorded, not asserted — the counts are the contract, the tags are evidence):
// the one-arg shape's survivors are exactly the args-spine `SCons` (size=40,
// tag 0x1) and the marshalled `SexpInt` (size=32, tag 0x0); the nullary shape's
// lone survivor is the JIT-built result cell.
//
// The fuller probe ladder — two invocations (+4), a larger argument sexp (+23),
// a quote-built identical result (+8, i.e. the quote path is balanced and NOT
// the producer), full stdlib (1143) — is recorded in
// `tests/plan/s118-test-plan.md` §2.5 and is not re-pinned here: these two cells
// carry the model's terms, and re-asserting the whole ladder would buy scale
// coverage at four more compiler children per run.
//
// SUPERSESSION NOTE (task 4 of the Branch-F change-set).
// `design/runtime/s118-structural-embedding-ownership.md` §6.3 obliged
// `/testing` to land ONE **prelude-face exact-BALANCE** cell in the W2b
// change-set — a fence for the ambient face, written on the assumption
// (§6.2's binding Branch-H prediction) that the W2b RE-1 fix would collapse the
// residual to 0. That prediction FAILED: the P-ladder was byte-identical
// pre/post-W2b, Branch F fired, and the face was attributed to a different seam
// entirely (the macro-turn marshal boundary, not the 0835/RE runtime pair). An
// exact-balance prelude-face cell would therefore have been a permanent RED
// asserting a contract no scheduled work could satisfy. **This file is the
// §6.3 obligation's successor and discharges it**: the same face, the same
// minimal shape §6.2 named (the P3 two-module, one-invocation form), fenced at
// the documented residual instead of at zero.
//
// spec anchor: the residual is a violation of `spec/12-runtime.md` §12.3.1
// (allocations are freed when no longer reachable). These cells hold the
// violation's magnitude; `design/arch/fixmes/0889-*.md` holds the obligation to
// remove it.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, MarginalPair};

/// The measured program is deliberately trivial and IDENTICAL on both sides:
/// the workload under measurement is the prelude's macro invocation, not
/// anything the program does.
const TRIVIAL_PROGRAM: &str = "(import [primitives [Pure]])\n\
     (defn main [] (Pure 0))\n";

/// A two-module mini-prelude. `macdef.cl` defines the macro, `macuse.cl` is the
/// only thing that differs between control and subject.
fn mini_prelude(macro_name: &str, macdef: &str, macuse: &str) -> Child {
    Child::new(TRIVIAL_PROGRAM)
        .lib_file(
            "prelude.cl",
            &format!("(export [macdef [{macro_name}]])\n(export [macuse [use-one]])\n"),
        )
        .lib_file("macdef.cl", macdef)
        .lib_file("macuse.cl", macuse)
}

// PIN — one macro expansion with ONE marshalled argument leaks EXACTLY 2 cells:
// the marshalled `SexpInt` argument and the `SCons` args spine. The expansion's
// result aliases its argument here (`` `~x ``), so the result term is 0 and this
// number is the ARGUMENT half of the closed form on its own.
//
// Control and subject differ by one character sequence — `41` vs `(ident 41)` —
// with the same modules, the same import of the same macro, and the same
// everything else. Defining and importing a macro without invoking it leaks
// nothing (plan §2.5 probes P1/P2 = 0), which is what makes this control valid.
//
// spec: spec/12-runtime.md §12.3.1 — every allocation is freed when it becomes
// unreachable; the macro-turn marshal boundary does not free these two.
// defect: class=rc-miscount locus=src/marshal.rs+src/expander.rs::invoke_clause found=S118 owner=/dev
#[test]
fn macro_turn_marshal_leak_documented_residual_one_expansion_with_one_marshalled_arg_is_two() {
    const MACDEF: &str = "(defmacro ident \"identity macro\" [x] `~x)\n";
    let m = MarginalPair::new(
        "one expansion of a one-argument macro",
        mini_prelude(
            "ident",
            MACDEF,
            "(import [macdef [ident]])\n(defn use-one [] 41)\n",
        ),
        mini_prelude(
            "ident",
            MACDEF,
            "(import [macdef [ident]])\n(defn use-one [] (ident 41))\n",
        ),
    )
    .measure();

    m.assert_residual(
        2,
        "FIXME 0889 — DOCUMENTED RESIDUAL PIN. One expansion of a one-argument \
         macro leaks exactly 2 cells (marshalled `SexpInt` + `SCons` args spine). \
         If this now reads 0 the leak has been FIXED: flip this cell's expected \
         value to 0, update `design/arch/fixmes/0889-*.md` and \
         `tests/plan/s118-test-plan.md` §2.5, and re-derive the ambient term the \
         retrofitted cells in `ms_p8_conj_leak.rs` and \
         `intrinsics_m3_detection_s116.rs` subtract. Any OTHER value means the \
         leak's magnitude or shape has changed and the closed-form model quoted \
         across the plan and the FIXME is now wrong.",
    );
}

// PIN — one NULLARY expansion whose body builds its result with `Sexp`
// constructors (no quote forms anywhere) leaks EXACTLY 1 cell: the JIT-built
// result tree's single cell. With no arguments there is nothing to marshal, so
// this number is the RESULT half of the closed form on its own — the term the
// one-argument pin above cannot see.
//
// This shape is also the Branch-F discriminator that excluded the
// `quote_sexp`/`quote_slist` path as the producer: a quote-built IDENTICAL
// result measures the same as a constructor-built one, so the quote path is
// balanced and the leak is on the marshal turn (plan §2.5, discriminator table).
//
// spec: spec/12-runtime.md §12.3.1 — every allocation is freed when it becomes
// unreachable; the un-consumed expansion result is not.
// defect: class=rc-miscount locus=src/marshal.rs+src/expander.rs::invoke_clause found=S118 owner=/dev
#[test]
fn macro_turn_marshal_leak_documented_residual_one_nullary_expansion_is_one() {
    const MACDEF: &str = "(import [macros [*]])\n\
         (defmacro two \"constructor-built nullary macro\" [] (SexpInt 2))\n";
    let m = MarginalPair::new(
        "one expansion of a nullary constructor-built macro",
        mini_prelude(
            "two",
            MACDEF,
            "(import [macdef [two]])\n(defn use-one [] 2)\n",
        ),
        mini_prelude(
            "two",
            MACDEF,
            "(import [macdef [two]])\n(defn use-one [] (two))\n",
        ),
    )
    .measure();

    m.assert_residual(
        1,
        "FIXME 0889 — DOCUMENTED RESIDUAL PIN. One nullary expansion leaks \
         exactly 1 cell (the never-consumed expansion-result tree; no arguments \
         are marshalled in this shape). If this now reads 0 the RESULT half of \
         the leak has been fixed — check the one-argument pin to see whether the \
         ARGUMENT half went with it, then update this cell, \
         `design/arch/fixmes/0889-*.md` and `tests/plan/s118-test-plan.md` §2.5.",
    );
}
