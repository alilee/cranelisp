//! The inline `div-i64` lowering (spec §12.7.3).
//!
//! Each probe is a real JIT function `probe(a, b) -> Int` whose body is the
//! production `div-i64` emission over the production `runtime/panic`. Only a
//! zero divisor raises; `Int.MIN / -1` wraps to `Int.MIN`. A raise ends the
//! process, so every cell calls the probe in a child (`crate::test_child`),
//! which also contains a Cranelift `sdiv` trap should the guard admit the
//! `MIN / -1` operand pair.

use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_types::Span;

use crate::jit::{Jit, declare_intrinsics_generic};
use crate::test_child;
use crate::test_support::assert_raise_terminates;

const CHILD: &str = "child_divides";

/// Marks the quotient on the child's stdout. libtest's `test … ` status may
/// precede it on the same line.
const QUOTIENT: &str = "QUOTIENT=";

struct Probe {
    jit: Jit,
    func: FuncId,
    clif: String,
    panic: FuncId,
}

fn build_probe() -> Probe {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let panic = declare_intrinsics_generic(module)
        .expect("declare intrinsics")
        .panic
        .expect("runtime/panic");
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let func = module
        .declare_function("div_probe", Linkage::Export, &sig)
        .expect("declare probe");
    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    let mut fctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let params = builder.block_params(entry).to_vec();
        let q = super::try_emit_inline_primitive(
            &mut builder,
            "div-i64",
            &params,
            Span::SYNTHETIC,
            module,
            Some(panic),
        )
        .expect("div-i64 is inline")
        .expect("div-i64 emits");
        builder.ins().return_(&[q]);
        builder.seal_all_blocks();
        builder.finalize();
    }
    let clif = ctx.func.display().to_string();
    module
        .define_function(func, &mut ctx)
        .expect("define probe");
    module.clear_context(&mut ctx);
    module.finalize_definitions().expect("finalize probe");
    Probe {
        jit,
        func,
        clif,
        panic: panic.func_id(),
    }
}

// Child body: print the quotient of `A` by `B`, then the resumed marker.
#[test]
fn child_divides() {
    if !test_child::selected(CHILD) {
        return;
    }
    let mut probe = build_probe();
    let code = probe.jit.jit_module().get_finalized_function(probe.func);
    let f: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(code) };
    let q = f(test_child::arg("A"), test_child::arg("B"));
    println!("{QUOTIENT}{q}");
    println!("{}", test_child::RESUMED);
}

fn divide_in_child(a: i64, b: i64) -> test_child::Ending {
    let path = test_child::child_path(module_path!(), CHILD);
    test_child::run(&path, &[("A", a.to_string()), ("B", b.to_string())])
}

/// Assert the child returned `expected` from `a / b` with no panic report.
#[track_caller]
fn assert_quotient(a: i64, b: i64, expected: i64) {
    let end = divide_in_child(a, b);
    let what = format!("{a} / {b}");
    assert_eq!(
        end.code,
        Some(0),
        "{what}: a normal exit, not a panic or trap\nstderr:\n{}",
        end.stderr
    );
    assert!(
        !end.stderr
            .contains(cranelisp_intrinsics::panic::PANIC_REPORT_PREFIX),
        "{what}: no panic report\n{}",
        end.stderr
    );
    let quotients: Vec<&str> = end
        .stdout
        .lines()
        .filter_map(|l| l.split_once(QUOTIENT).map(|(_, q)| q))
        .collect();
    assert_eq!(quotients, [expected.to_string().as_str()], "{what}");
    assert!(end.stdout.contains(test_child::RESUMED), "{what}");
}

// spec: spec/12-runtime.md §12.7.3 — `Int.MIN / -1` wraps to `Int.MIN` by the
// two's-complement rule of `+`, `-` and `*`, and does not panic.
#[test]
fn min_by_neg_one_wraps_to_min() {
    assert_quotient(i64::MIN, -1, i64::MIN);
}

// spec: spec/12-runtime.md §12.7.3 (NEGATIVE) — the `-1` divisor path is
// negation for every other dividend: it neither panics nor changes their
// quotients.
#[test]
fn other_dividends_by_neg_one_negate_neg() {
    for (a, q) in [
        (7, -7),
        (-7, 7),
        (0, 0),
        (i64::MAX, -i64::MAX),
        (i64::MIN + 1, i64::MAX),
    ] {
        assert_quotient(a, -1, q);
    }
}

// spec: spec/12-runtime.md §12.7.3 (NEGATIVE) — other divisors are truncating
// signed division, `Int.MIN` dividend included.
#[test]
fn other_divisors_truncate_neg() {
    for (a, b, q) in [
        (7, 2, 3),
        (-7, 2, -3),
        (7, -2, -3),
        (i64::MIN, 1, i64::MIN),
        (i64::MIN, 2, i64::MIN / 2),
        (i64::MIN, -2, i64::MIN / -2),
    ] {
        assert_quotient(a, b, q);
    }
}

// spec: spec/12-runtime.md §12.7.3 — a zero divisor still panics with
// "division by zero", for an ordinary dividend and for `Int.MIN`.
#[test]
fn zero_divisor_panics() {
    for a in [7, i64::MIN] {
        divide_in_child(a, 0).assert_panicked_with("division by zero", &format!("{a} / 0"));
    }
}

// spec: design/backend/backend.md §7 "One emission helper" — the lowering has
// exactly one raise, the zero-divisor guard, and it terminates its block. The
// `MIN / -1` pair reaches no raise.
#[test]
fn division_has_one_raise() {
    let probe = build_probe();
    assert_eq!(
        assert_raise_terminates(&probe.clif, probe.panic, "div-i64"),
        1,
        "{}",
        probe.clif
    );
}
