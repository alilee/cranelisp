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

    m.assert_balanced(
        "a successful nullary macro expansion must discharge its constructor-built \
         expansion-result tree exactly once",
    );
}
