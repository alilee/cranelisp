//! S118 W3 (FIXME 0893) — the §6 row-4 narrowing, pinned at the FACT-GATHERING
//! seam it lives at, through a COMPILED shape.
//!
//! `tco_slot_predicate_tests` pins [`super::tco_slot_disposition`], the pure
//! verdict, by constructing a `TailSlotFacts` directly. That leaves the actual
//! defect direction unguarded: `tail_transfer_skip` is SPELLING-based, so the
//! judgment "this slot's owner travels into the next iteration" was made without
//! ever asking whether the named binding is borrowed. A borrowed inner binder
//! that SHADOWS a frame-owned parameter therefore licensed a transfer on the
//! strength of an alias holding no reference at all — the param slot's release
//! was skipped and the surviving iteration ran on a freed box (the UAF
//! direction). A regression that stops [`super::FnCompiler::tail_slot_facts`]
//! setting `bare_var_arg_is_borrowed` leaves the pure-predicate cell green.
//!
//! These cells compile real bodies through the production per-body seam
//! (`test_support::try_compile_defns_in_module` → `compile_defn_in_module`) and
//! read the compiler's answer, not a struct:
//!
//! * `(defn go [n x] (let [x x] (go 0 x)))` — the inner `let` binds the SAME
//!   spelling as the heap-typed parameter, and a `let` whose value forwards a
//!   live binding is marked borrowed (`operand_live_binding_root`). The tail
//!   argument `x` therefore names the parameter's slot but resolves to the
//!   borrowed alias. The compiler must REFUSE (`SlotDisposition::BorrowedInvalid`
//!   reported by `check_no_borrowed_transfer`), never silently skip the slot's
//!   release.
//! * `(defn go [n x] (go 0 x))` — the non-shadowing control, in BOTH parameter
//!   modes. Row 4 is not "the slot is borrowed": a `Borrowed` parameter carried
//!   forward as its own tail argument is the ordinary shape and the frame owes
//!   nothing, so it must compile. This is the fence against the over-broad first
//!   version of the fix (the one measured wrong at 8 red e2e cells).
//!
//! **Falsification (RED-first, the W2b 0885 pattern).** Both directions were run
//! against broken forms of `tail_slot_facts`:
//!
//! * UNDER-NARROW (`bare_var_arg_is_borrowed: false` — the original defect):
//!   `a_shadowing_borrow_cannot_license_the_param_slot_transfer_neg` FAILED with
//!   `the shadowing-borrow shape must be REFUSED ...; it compiled instead`. The
//!   controls stayed green, which is exactly why they cannot substitute for it.
//! * OVER-BROAD (`named && self.is_borrowed(name)`, dropping the shadowing
//!   conjunct): `a_borrowed_parameter_carried_forward_is_not_a_shadowing_borrow`
//!   FAILED with `a Borrowed parameter carried forward as its own tail argument
//!   is ordinary ...: tail self-call in 'go' offers the BORROWED alias 'x' ...`.
//!   The negative cell stayed green, so it cannot substitute either.

use std::collections::HashMap;

use cranelisp_types::{
    CranelispError, Defn, DefnVariant, Expr, FQSymbol, Mode, ModeSummary, ModuleFullPath, Span,
    Symbol, SymbolTable, Type, Visibility,
};

const GO: &str = "go";

fn module_path() -> ModuleFullPath {
    ModuleFullPath::from("user")
}

fn var(name: &str, span: Span, ty: Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

/// `(go 0 <second>)` in tail position. The literal first argument keeps `n` out
/// of `tail_transfer_skip`, so the cells isolate the second slot.
fn tail_self_call(second: Expr) -> Expr {
    Expr::Apply {
        callee: Box::new(var(
            GO,
            Span::new(201, 203),
            Type::Fn(vec![Type::Int, Type::String], Box::new(Type::Int)),
        )),
        args: vec![
            Expr::IntLit {
                value: 0,
                span: Span::new(204, 205),
                inferred_type: Some(Box::new(Type::Int)),
            },
            second,
        ],
        span: Span::new(200, 210),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// `(defn go [n x] <body>)` with `x` heap-typed (`String`).
fn go_defn(body: Expr) -> Defn {
    Defn {
        name: Symbol::from(GO),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("n"), None), (Symbol::from("x"), None)],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

/// Compile `defn` through the production per-body seam with the given ownership
/// summary, returning the compiler's verdict. The callee `Var` carries the
/// current fn's storage FQ — typecheck's self-recursion signal, without which
/// fast-path 1 never reaches the tail-jump flushes at all.
fn compile(defn: &Defn, summary: Option<ModeSummary>) -> Result<String, CranelispError> {
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("JIT construction");
    let module_path = module_path();

    let symbol_tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let mut st = SymbolTable::new(module_path.clone());
    // The entry's `Scheme.ty` is where `bind_defn_params` reads param types
    // from: `x` MUST be `String` or nothing in this file is heap-classified.
    crate::test_support::insert_user_fn_stub_typed(
        &mut st,
        GO,
        &[Type::Int, Type::String],
        Type::Int,
    );
    symbol_tables.insert(module_path.clone(), st);

    let resolved_targets: HashMap<Span, FQSymbol> =
        crate::test_support::call_carriers(defn.body(), &module_path, &[GO]);

    crate::test_support::try_compile_defns_in_module(
        &[defn],
        &[summary],
        &[],
        &resolved_targets,
        &symbol_tables,
        module_path,
        jit.jit_module(),
    )
    .map(|mut clifs| clifs.pop().expect("one compiled defn"))
}

/// `x` is `Borrowed` — the caller owns the reference.
fn borrowed_x() -> ModeSummary {
    ModeSummary {
        param_modes: vec![Mode::Copy, Mode::Borrowed],
        ..ModeSummary::default()
    }
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE — `transitive-drop-glue.md` §6
// row 4 / §10 row 6, "borrowed alias cannot license transfer") — a borrowed
// binding that SHADOWS a frame-owned parameter slot and is handed forward as
// that slot's tail argument carries no independently owned reference. The
// transfer is refused with a located error naming the alias; the silent
// alternative skips the slot's release and the next iteration runs on a box
// whose last owner has been discharged.
//
// defect: class=tco-shadowing-borrow-transfer locus=FnCompiler::tail_slot_facts found=S118 owner=/dev
#[test]
fn a_shadowing_borrow_cannot_license_the_param_slot_transfer_neg() {
    // (defn go [n x] (let [x x] (go 0 x)))
    let body = Expr::Let {
        bindings: vec![(
            Symbol::from("x"),
            var("x", Span::new(101, 102), Type::String),
        )],
        body: Box::new(tail_self_call(var("x", Span::new(206, 207), Type::String))),
        span: Span::new(100, 220),
        inferred_type: Some(Box::new(Type::Int)),
    };

    let err = compile(&go_defn(body), None).err().unwrap_or_else(|| {
        panic!(
            "the shadowing-borrow shape must be REFUSED at the tail self-call — \
             the inner `x` is a borrowed alias of the parameter and cannot \
             license the transfer of the parameter's own frame-owned slot; it \
             compiled instead, which is the silent-skip (UAF) direction"
        )
    });
    let text = err.to_string();
    assert!(
        text.contains("BORROWED alias 'x'"),
        "the report must name the offending alias: {text}"
    );
    assert!(
        text.contains("cannot license an ownership transfer"),
        "the report must name the refused claim: {text}"
    );
    assert!(
        text.contains(GO),
        "the report must name the requesting function: {text}"
    );
}

// spec: spec/12-runtime.md §12.3.1 — the non-shadowing control, and the fence
// against the over-broad narrowing. Row 4 is the SHADOWING case, not "the slot
// is borrowed": `(defn go [:Int n :String x] … (go 0 x))` with `x` inferred
// `Borrowed` is the ordinary carried-forward parameter — the frame owns nothing
// and owes nothing, so it must compile, in BOTH parameter modes.
#[test]
fn a_borrowed_parameter_carried_forward_is_not_a_shadowing_borrow() {
    // (defn go [n x] (go 0 x))
    let body = tail_self_call(var("x", Span::new(206, 207), Type::String));
    let defn = go_defn(body);

    let borrowed = compile(&defn, Some(borrowed_x()));
    assert!(
        borrowed.is_ok(),
        "a Borrowed parameter carried forward as its own tail argument is \
         ordinary and owes no release; widening row 4 to every borrowed slot \
         hard-errors on the common loop shape: {}",
        borrowed.err().map(|e| e.to_string()).unwrap_or_default()
    );

    let owned = compile(&defn, None);
    assert!(
        owned.is_ok(),
        "an OWNED parameter carried forward is the plain row-1 move and must \
         still compile: {}",
        owned.err().map(|e| e.to_string()).unwrap_or_default()
    );
}
