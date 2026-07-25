//! S97 — the lenient apply-argument spark pre-pass MUST exclude the inline IO
//! combinators (`bind` / `select` / `race` / `sleep`).
//!
//! Pins the seam of the `race`-with-inline-`bind`-lambda-branch lambda-name
//! collision (`tests/regression.rs::
//! race_with_inline_bind_lambda_branch_compiles_under_lenient`). `(race a b)`
//! has two sparkable IO-sub-tree args; without the exclusion the spark pre-pass
//! wraps each in a Phase-1 thunk, then `compile_race` RECOMPILES the same args
//! via `compile_vec_lit` (which does not consult `sparked_args`), re-emitting the
//! inner `(fn …)` at the same source span → two `__lambda_<span>__` declarations
//! with incompatible signatures (`{1 param}` thunk vs `{2 param}` closure). These
//! combinators compile their own arguments as IO sub-trees, so they must never
//! enter the value-sparking pre-pass.

use super::is_io_combinator_call;
use cranelisp_types::{JitSymbol, ResolvedCall, Symbol};

fn builtin(name: &str) -> ResolvedCall {
    ResolvedCall::BuiltinFn {
        name: Symbol::from(name),
    }
}

#[test]
fn io_combinators_are_excluded_from_the_spark_pre_pass() {
    for name in ["bind", "select", "race", "sleep"] {
        assert!(
            is_io_combinator_call(Some(&builtin(name))),
            "`{name}` compiles its own IO-sub-tree args and MUST be excluded from \
             the lenient apply-argument spark pre-pass (else the race/compile_vec_lit \
             recompilation collides on the `__lambda_<span>__` symbol)"
        );
    }
}

#[test]
fn non_combinator_builtins_and_other_calls_are_not_excluded() {
    // An ordinary builtin (a genuine value-arg apply) still goes through the
    // spark pre-pass — the exclusion must be narrow.
    for name in ["add-i64", "vec-get", "foo", "Pure"] {
        assert!(
            !is_io_combinator_call(Some(&builtin(name))),
            "`{name}` is not an inline IO combinator — it must NOT be excluded"
        );
    }
    // A non-BuiltinFn resolution (e.g. a sig-dispatched user fn) is never excluded.
    assert!(!is_io_combinator_call(Some(&ResolvedCall::SigDispatch {
        mangled_name: JitSymbol::from("user-fn$Int"),
    })));
    // No resolution at all (a closure-value call) is never excluded.
    assert!(!is_io_combinator_call(None));
}
