// macro_turn_marshal_leak_0889.rs — macro-turn discharge acceptance fences.
//
// S122 Q4 requires successful macro expansion to discharge both the marshalled
// argument tree and the returned expansion tree. These marginal pairs isolate
// those terms with one extra expansion and require exact balance. Before the
// runtime migration, the one-argument subject retains +2 cells and the nullary
// subject retains +1; those measurements are the intended RED before-state.
//
// The original S118 probe ladder, allocation fingerprints, and full-prelude
// observation are retained as historical evidence in
// `tests/plan/s118-test-plan.md` §2.5. They are not acceptance thresholds.
//
// spec: `spec/12-runtime.md` §12.3.1 — allocations are freed when no longer
// reachable.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::marginal::{Child, Marginal, MarginalPair};

/// The measured program is deliberately trivial and IDENTICAL on both sides:
/// the workload under measurement is the prelude's macro invocation, not
/// anything the program does.
const TRIVIAL_PROGRAM: &str = "(import [primitives [Pure]])\n\
     (defn main [] (Pure 0))\n";

/// A two-module mini-prelude. `macdef.cl` defines the macro, `macuse.cl` is the
/// only thing that differs between control and subject. Both open with the null
/// import: the prelude loads them, so the implicit prelude import would close a
/// cycle (spec §8.8.1) and both children would fail alike.
fn mini_prelude(macro_name: &str, macdef: &str, macuse: &str) -> Child {
    const OPT_OUT: &str = "(import [prelude []])\n";
    Child::new(TRIVIAL_PROGRAM)
        .lib_file(
            "prelude.cl",
            &format!("(export [macdef [{macro_name}]])\n(export [macuse [use-one]])\n"),
        )
        .lib_file("macdef.cl", &format!("{OPT_OUT}{macdef}"))
        .lib_file("macuse.cl", &format!("{OPT_OUT}{macuse}"))
}

/// A pair whose children fail alike measures 0, so each must run to exit 0.
fn assert_children_succeeded(m: &Marginal) {
    assert!(
        m.control().exit_code() == Some(0) && m.subject().exit_code() == Some(0),
        "both children must exit 0\n{}\n--- control stderr ---\n{}\n--- subject stderr ---\n{}",
        m.report(),
        m.control().stderr,
        m.subject().stderr
    );
}

// S122 Q4 acceptance — one macro expansion with ONE marshalled argument must
// balance. The pre-fix before-state is exactly +2 cells:
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
fn macro_turn_marshal_one_argument_expansion_is_balanced() {
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

    assert_children_succeeded(&m);
    m.assert_balanced(
        "a successful one-argument macro expansion must discharge the marshalled \
         `SexpInt`, its `SCons` argument spine, and the returned alias exactly once",
    );
}

// S122 Q4 acceptance — one NULLARY expansion whose body builds its result with
// `Sexp` constructors (no quote forms anywhere) must balance. Its pre-fix
// before-state is exactly +1 cell: the JIT-built result tree. With no arguments
// this isolates the RESULT half of the discharge contract.
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
fn macro_turn_marshal_nullary_expansion_is_balanced() {
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

    assert_children_succeeded(&m);
    m.assert_balanced(
        "a successful nullary macro expansion must discharge its constructor-built \
         expansion-result tree exactly once",
    );
}

// ACT-0976 (S122 K2) — a macro clause that raises a language runtime error
// leaves no residue beyond a successful twin's. The runtime error sets the
// error flag and returns without the clause's compiled cleanup, and the host
// discards the returned word, so any stranded argument or frame value would
// read positive here.
//
// A REPL pair, since a failed expansion ends a batch compile before its exit
// report. Both sessions define both macros and marshal the same `42`; the
// invocation turn alone differs, `(okm 42)` versus `(boom 42)`. The last turn
// shows each session continued.
//
// On 2026-09-30 (source `f0d1006f…`) the control balanced at 2/2 and the
// subject read 2 allocations, 0 frees: the marshalled argument's two cells
// stay live, with no seam violation. Attribution is QA's (ACT-0976).
//
// spec: spec/09-macros.md §9.9.4 — a runtime error during expansion is a clean
// error at the call site; spec/12-runtime.md §12.3.1 — every allocation is
// freed when it becomes unreachable.
// defect: class=rc-miscount locus=src/expander.rs::invoke_clause found=S122 owner=/dev
#[test]
fn macro_runtime_error_expansion_balances_against_successful_twin() {
    let session = |call: &str| {
        Child::repl(&format!(
            "(import [primitives [div-i64]])\n\
             (defmacro okm [x] (let [_ (div-i64 1 1)] x))\n\
             (defmacro boom [x] (let [_ (div-i64 1 0)] x))\n\
             {call}\n\
             (div-i64 84 2)\n"
        ))
        .env("CRANELISP_RC_DEC_CHECK", "1")
    };
    let m = MarginalPair::new(
        "a macro expansion ending in a runtime error",
        session("(okm 42)"),
        session("(boom 42)"),
    )
    .measure();

    assert_children_succeeded(&m);
    assert!(
        m.subject().stdout.to_lowercase().contains("error")
            && !m.control().stdout.to_lowercase().contains("error")
            && m.subject().stdout.contains("42"),
        "only the subject's expansion fails, and its session continues\n{}\n\
         --- control stdout ---\n{}\n--- subject stdout ---\n{}",
        m.report(),
        m.control().stdout,
        m.subject().stdout
    );
    m.assert_balanced(
        "a macro expansion ending in a runtime error must leave no residue beyond \
         its successful twin",
    );
}
