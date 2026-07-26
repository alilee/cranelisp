//! S115 W4c / FIXME 0781 — the match seam's scrutinee-ownership gate is the
//! value's PROVENANCE, not the node kind.
//!
//! `compile_var_pattern_arm`'s `is_alias` and `dec_temporary_scrutinee`'s
//! `is_temp` are the same question asked with opposite polarity: does THIS
//! frame own the scrutinee's value? Both used to answer
//! `matches!(scrutinee, MonoExpr::Var { .. })`, so an `If`/`Match`/`Let` that
//! merely YIELDS a borrowed param was registered for scope cleanup AND dec'd
//! as a temporary — two releases of a box the caller already owns.
//!
//! Measured before the fix, `PrimitivesOnly`, `--link`:
//! `(defn f [v b] (match (if b v v) [xs (vec-get xs 0)]))` → exit 134
//! "corrupted double-linked list"; the `let`-yielding-a-binding twin
//! `(match (let [w v] w) …)` and the ADT-pattern twin
//! `(match (if b t t) [(Wrap xs) …])` abort identically. All three exit 9
//! (clean) after routing both gates through
//! `fn_compiler::yields_owned_temporary`.
//!
//! DETECTION PROOF: restoring either `matches!(.., MonoExpr::Var { .. })` test
//! flips `if_joined_borrowed_param_scrutinee_is_not_released_neg` RED (the dec
//! count rises from 1); the control below stays GREEN in both states, so the
//! pair discriminates "the gate narrowed correctly" from "the release was
//! deleted".

use crate::jit::Jit;
use cranelisp_types::{Defn, DefnVariant, Expr, MatchArm, Pattern, Span, Symbol, Type, Visibility};
use std::collections::HashMap;

/// Compile `(defn probe <params> <body>)` and return the emitted CLIF.
fn clif_of(body: Expr, params: Vec<(Symbol, Option<cranelisp_types::TypeExpr>)>) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let defn = Defn {
        name: Symbol::from("scrutinee_ownership_probe"),
        docstring: None,
        variants: vec![DefnVariant {
            params,
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let symbol_tables: dashmap::DashMap<
        cranelisp_types::ModuleFullPath,
        cranelisp_types::SymbolTable,
    > = dashmap::DashMap::new();
    let module_path = cranelisp_types::ModuleFullPath::from("user");
    symbol_tables.insert(
        module_path.clone(),
        cranelisp_types::SymbolTable::new(module_path.clone()),
    );
    let no_targets: HashMap<Span, cranelisp_types::FQSymbol> = HashMap::new();
    crate::test_support::probe_defn_clif(
        &defn,
        &[],
        &no_targets,
        &symbol_tables,
        module_path,
        jit.jit_module(),
    )
}

/// Count the canonical drop-glue calls in a rendered CLIF body.
///
/// Canonical glue has the release ABI `(i64) -> ()` — one heap word in, nothing
/// out — so its signature is unmistakable in the CLIF preamble
/// (`sigN = (i64) system_v`), and every `fnM` declared against such a sig is a
/// release. This counts calls to those, which is the "exactly one release per
/// consuming arm" instrument §7.3 asks for. (`runtime/dealloc` shares the ABI
/// but is only reached from INSIDE a glue body — never emitted into a user body
/// once the migration is complete.)
fn release_abi_calls(clif: &str) -> usize {
    let release_sigs: Vec<&str> = clif
        .lines()
        .filter_map(|l| {
            let l = l.trim();
            let (name, rest) = l.split_once(" = ")?;
            (name.starts_with("sig") && rest == "(i64) system_v").then_some(name)
        })
        .collect();
    let release_fns: Vec<&str> = clif
        .lines()
        .filter_map(|l| {
            let l = l.trim();
            let (name, rest) = l.split_once(" = ")?;
            let sig = rest.rsplit(' ').next()?;
            (name.starts_with("fn") && release_sigs.contains(&sig)).then_some(name)
        })
        .collect();
    clif.lines()
        .filter(|l| {
            release_fns
                .iter()
                .any(|f| l.contains(&format!("call {f}(")))
        })
        .count()
}

fn vec_ty() -> Type {
    Type::ADT(
        cranelisp_types::FQTypeName::new(
            cranelisp_types::ModuleFullPath::from("primitives"),
            cranelisp_types::TypeName::from("Vec"),
        ),
        vec![Type::Int],
    )
}

fn int_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn var(name: &str, ty: Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

fn vec_lit() -> Expr {
    Expr::VecLit {
        elements: vec![int_lit(7), int_lit(8), int_lit(9)],
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(vec_ty())),
    }
}

/// `(vec-get <container> 0)`.
fn vec_get_of(container: Expr) -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("vec-get"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: None,
        }),
        args: vec![container, int_lit(0)],
        span: Span::SYNTHETIC,
        resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("vec-get"),
        })),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// `(match <scrutinee> [xs (vec-get xs 0)])` — a var-pattern arm whose body
/// does NOT forward the scrutinee, so the consume path runs.
fn match_reading_scrutinee(scrutinee: Expr) -> Expr {
    Expr::Match {
        scrutinee: Box::new(scrutinee),
        arms: vec![MatchArm {
            pattern: Pattern::Var {
                name: Symbol::from("xs"),
                span: Span::SYNTHETIC,
            },
            body: vec_get_of(var("xs", vec_ty())),
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
        compiler_generated: false,
    }
}

/// `(match <scrutinee> [xs xs])` — a var arm that FORWARDS the whole scrutinee.
fn match_forwarding_scrutinee(scrutinee: Expr) -> Expr {
    Expr::Match {
        scrutinee: Box::new(scrutinee),
        arms: vec![MatchArm {
            pattern: Pattern::Var {
                name: Symbol::from("xs"),
                span: Span::SYNTHETIC,
            },
            body: var("xs", vec_ty()),
            span: Span::SYNTHETIC,
        }],
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(vec_ty())),
        compiler_generated: false,
    }
}

/// `(if b v v)` over a borrowed `(Vec Int)` param.
fn if_joined_param() -> Expr {
    Expr::If {
        cond: Box::new(var("b", Type::Bool)),
        then_branch: Box::new(var("v", vec_ty())),
        else_branch: Box::new(var("v", vec_ty())),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(vec_ty())),
    }
}

// spec: spec/12-runtime.md §12.1 / FIXME 0781 — a match scrutinee that merely
// YIELDS a borrowed binding is not this frame's to release. With Int elements
// and an Int result the only legitimate rc dec in this body is the Decision-24
// scope-exit release of the owned `v` param; the defect added the scrutinee
// temp-dec and the pattern-alias cleanup dec on top of it.
// MEASURED: `--link` exit 134 before, exit 9 after.
#[test]
fn if_joined_borrowed_param_scrutinee_is_not_released_neg() {
    let clif = clif_of(
        match_reading_scrutinee(if_joined_param()),
        vec![(Symbol::from("v"), None), (Symbol::from("b"), None)],
    );
    let decs = clif.matches("atomic_rmw.i64 sub").count();
    assert_eq!(
        decs, 1,
        "an `If` joining two BORROWED arms yields the caller's vector: neither \
         the scrutinee temp-dec nor the pattern-alias scope cleanup may claim \
         it (FIXME 0781, `--link` exit 134). Expected exactly the one \
         scope-exit dec, found {decs}. CLIF:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.1 / FIXME 0781 + 0782 — the DISCRIMINATING
// CONTROL (METHOD §2.2 "only a control confirms a mechanism"): the same match
// over a FRESH vec literal IS this frame's temporary, and its release must
// survive the narrowing. Without this cell the negative above would also pass
// if the release had simply been deleted.
//
// S118 slice S3 supersedes the deliberately loose S115 "at least one release"
// pin with a COUNT (`transitive-drop-glue.md` §7.3): the release-exactly-once
// face is precisely what 0782 got wrong — HEAD emitted the merge-block dec AND
// registered the var binder for scope cleanup, two `atomic_rmw sub` on one
// value. An exact-balance instrument is blind to a double release of a value
// that was going to be freed anyway, so the count lives here in the unit tier.
//
// The release is now a `call` to the scrutinee type's canonical drop glue, so
// the count is of release-ABI calls rather than of inline atomics.
#[test]
fn consuming_arm_releases_the_owned_scrutinee_exactly_once() {
    let clif = clif_of(match_reading_scrutinee(vec_lit()), vec![]);
    let releases = release_abi_calls(&clif);
    assert_eq!(
        releases, 1,
        "a FRESH vec-literal scrutinee is an owned temporary consumed by its \
         arm: EXACTLY one release, at the arm's lifetime end. Found {releases}. \
         0 = the 0781 narrowing became a leak; 2 = the 0782 double-release is \
         back. CLIF:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.1 / FIXME 0782 — the FORWARDING polarity of the
// same seam, and the reason the count above is a count. A var arm that forwards
// the whole scrutinee out (`[xs xs]`) carries the one owner to the outer
// consume position, so this path emits NO release. The pair discriminates
// "released once at the right place" from "released whenever".
#[test]
fn forwarding_var_arm_over_an_owned_temporary_emits_no_release_neg() {
    let clif = clif_of(match_forwarding_scrutinee(vec_lit()), vec![]);
    let releases = release_abi_calls(&clif);
    assert_eq!(
        releases, 0,
        "a var arm that forwards the whole scrutinee transfers the single \
         owner out; releasing it here frees a value that travels. Found \
         {releases}. CLIF:\n{clif}"
    );
}

// spec: spec/12-runtime.md §12.1 / FIXME 0781 — a bare `Var` scrutinee is
// unchanged by the narrowing (the shape test and the provenance answer agree
// on every `Var`), so this cell is the byte-level no-regression fence for the
// overwhelmingly common shape.
#[test]
fn bare_var_scrutinee_is_unchanged_by_the_narrowing() {
    let clif = clif_of(
        match_reading_scrutinee(var("v", vec_ty())),
        vec![(Symbol::from("v"), None)],
    );
    let decs = clif.matches("atomic_rmw.i64 sub").count();
    assert_eq!(
        decs, 1,
        "a bare `Var` scrutinee is dec'd by its owning scope exactly once — the \
         provenance gate must agree with the old shape test here. Found {decs}. \
         CLIF:\n{clif}"
    );
}
