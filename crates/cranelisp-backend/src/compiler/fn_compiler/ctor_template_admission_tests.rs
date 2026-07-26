//! S118 — `design/backend/transitive-drop-glue.md` §4.1 (the ruling) and §10
//! row 4: the ONE sanctioned non-concrete release site is the **constructor
//! template's own parameter**, and §4.1 rules that the gate admitting it must be
//! keyed on the **frame**, never on the type. That ruling has NOT shipped — the
//! live gate is type-keyed, knowingly; see the measurement below.
//!
//! A constructor `Def` is compiled ONCE per declaration, so its parameter types
//! come from the entry's `scheme` and two legal declaration shapes hand that
//! scheme a non-concrete parameter — a generic field (`(deftype (Option a)
//! (Some [:a v]))`) and an undeclared field (`(deftype B (Mk [v]))`). In that
//! frame the scope-exit release is not a teardown: it is the balancing half of
//! the guarded consuming inc `compile_consuming_arg_list` emitted on the same
//! value, on a word the returned box now also holds (invariant **I-CT**), so the
//! shallow dec can never observe the last reference.
//!
//! **What these cells fence, and what they deliberately do NOT.** These are §10
//! row 4's positive and edge cells: the balance itself, for both non-concrete
//! template shapes and for the multi-field case, plus the boundary that being a
//! ctor template is *necessary but not sufficient* (a concrete field takes the
//! ordinary `drop<T>` path). They hold under any admission key.
//!
//! The "same predicate / no polarity gap" half of I-CT is asserted as CONTROL
//! FLOW by [`assert_threshold_guarded_rmws`] — each `atomic_rmw` is traced back to
//! the comparison and branch arm that admit its block — not by counting
//! `iconst.i64 1024` occurrences, which an inverted dec-side comparison satisfies
//! exactly while breaking the invariant (FIXME 0905; §10's own standard, "assert
//! emitted call identity and control-flow ordering, not only text presence").
//!
//! Row 4's **negative** half — "a non-concrete binding in a NON-ctor-template
//! frame is a located error" — is **not landed here**, and the reason is a
//! measurement, not an omission. §4.1's gate was implemented as ruled (a
//! frame-level `is_ctor_template` boolean computed in `compile_body` from the
//! body node, threaded to the shared release body as a two-state
//! `NonConcreteRelease` verdict, with both tail-jump flushes passing the
//! rejecting arm) and the negatives went RED-then-GREEN exactly as designed —
//! but the corpus went the other way:
//!
//! * baseline `binary(/^spec_/)`: 893 run, 8 pre-existing failures;
//! * under the ruled frame key: 893 run, **24** failures — 16 NEW hard codegen
//!   refusals across `spec_03_types` (7), `spec_07_traits` (5),
//!   `spec_field_accessor` (2), `spec_04_expressions` (1),
//!   `spec_05_definitions` (1).
//!
//! Two further families reach the arm in ordinary `defn`-shaped frames that
//! I-CT does not cover: synthetic **field accessors** of a generic or
//! undeclared-field product (`Box.v`'s `self: ADT(user/Box, [Var(0)])`) and
//! generic **trait-method instances** (`Functor.fmap$primitives/Option`'s
//! `Fn([Var(9)], Var(8))` parameter). So §4.1's premise — "the migration
//! measured exactly one class" — is false, and the narrowing cannot land until
//! the whole measured class is ruled: FIXME 0903 → `/design`(backend), which
//! carries the implemented gate and both negative cells verbatim for re-landing.
//!
//! The consequence for a reader of THIS file: the cells below pass under the
//! type-keyed gate that is still in place *and* under the frame key that will
//! replace it. They are not evidence that the key is right.

use std::collections::HashMap;

use dashmap::DashMap;

use cranelisp_types::{
    CranelispError, DefKind, Defn, DefnVariant, Expr, FQSymbol, FQTypeName, HeapHeader, ModuleEntry,
    ModuleFullPath, Scheme, Span, Symbol, SymbolTable, Type, TypeDefInfo, TypeName, Visibility,
    NULLARY_TAG_THRESHOLD,
};

use crate::test_support::count_release_ops;

/// The nullary-tag discriminator, as it renders in CLIF. Used ONLY for the
/// negative cell (`AlwaysHeap` field ⇒ the constant must not appear at all).
///
/// It is deliberately NOT how the positive cells assert the shared predicate:
/// counting threshold constants is text presence standing in for structure, and
/// an inverted dec-side comparison keeps the count exact while breaking I-CT in
/// the polarity-gap direction (FIXME 0905). The positive cells use
/// [`assert_threshold_guarded_rmws`], which walks the control flow.
const NULLARY_GUARD: &str = "iconst.i64 1024";

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

/// A constructor template `(deftype T (Ctor [f0 f1 …]))`: the synthetic
/// `Expr::ConstrADT` body typecheck synthesises for the constructor `Def`, plus
/// the symbol tables that give it its signature.
///
/// `fields` carries each field's SIGNATURE type — the `scheme` is where
/// `bind_defn_params` reads parameter types from, so this is the ONLY place the
/// non-concreteness under test can be spelled.
fn ctor_template(
    type_name: &str,
    ctor: &str,
    fields: &[(&str, Type)],
) -> (Defn, DashMap<ModuleFullPath, SymbolTable>) {
    let module = module_path();
    let fqtn = FQTypeName::new(module.clone(), TypeName::from(type_name));
    let adt = Type::ADT(fqtn.clone(), vec![]);

    let field_exprs: Vec<Expr> = fields
        .iter()
        .enumerate()
        .map(|(i, (name, ty))| {
            let base = 100 + (i as u32) * 10;
            var(name, Span::new(base, base + 1), ty.clone())
        })
        .collect();

    let body = Expr::ConstrADT {
        type_name: fqtn.clone(),
        tag: 0,
        fields: field_exprs,
        span: Span::new(10, 90),
        inferred_type: Some(Box::new(adt.clone())),
    };

    let defn = Defn {
        name: Symbol::from(ctor),
        docstring: None,
        variants: vec![DefnVariant {
            params: fields
                .iter()
                .map(|(name, _)| (Symbol::from(*name), None))
                .collect(),
            body,
            span: Span::new(0, 100),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 100),
    };

    let mut st = SymbolTable::new(module.clone());
    st.insert(
        Symbol::from(type_name),
        ModuleEntry::TypeDef {
            info: TypeDefInfo {
                name: fqtn.clone(),
                type_params: vec![],
                constructors: vec![Symbol::from(ctor)],
            },
            visibility: Visibility::Public,
            docstring: None,
        },
    );
    st.insert(
        Symbol::from(ctor),
        ModuleEntry::Def {
            scheme: Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(
                    fields.iter().map(|(_, ty)| ty.clone()).collect(),
                    Box::new(adt),
                ),
            },
            visibility: Visibility::Public,
            docstring: None,
            param_names: fields.iter().map(|(name, _)| Symbol::from(*name)).collect(),
            kind: Box::new(DefKind::Constructor {
                got_slot: 0,
                type_name: fqtn,
                tag: 0,
                field_count: fields.len(),
                internal: false,
                type_def: None,
                mode_summary: None,
            }),
            callees: vec![],
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        },
    );

    let tables = DashMap::new();
    tables.insert(module, st);
    (defn, tables)
}

/// Compile `defn` through the production per-body seam and return the compiler's
/// verdict (CLIF text, or the located refusal).
fn compile(
    defn: &Defn,
    tables: &DashMap<ModuleFullPath, SymbolTable>,
) -> Result<String, CranelispError> {
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = module_path();
    // A ctor template's body is one straight-line construction: no calls, so no
    // dispatch carriers to thread.
    let resolved_targets: HashMap<Span, FQSymbol> = HashMap::new();
    crate::test_support::try_compile_defns_in_module(
        &[defn],
        &[],
        &[],
        &resolved_targets,
        tables,
        module,
        jit.jit_module(),
    )
    .map(|mut clifs| clifs.pop().expect("one compiled defn"))
}

fn count(clif: &str, needle: &str) -> usize {
    clif.matches(needle).count()
}

// ---------------------------------------------------------------------------
// Structural CLIF walk: which predicate admits each `atomic_rmw`, and on which
// arm (FIXME 0905 — §10's own standard, "control-flow ordering, not only text
// presence").
// ---------------------------------------------------------------------------

/// Which arm of a `brif` a basic block sits on.
#[derive(Debug, PartialEq, Eq)]
enum BrifArm {
    /// The condition-TRUE target.
    Taken,
    /// The condition-FALSE (fall-through) target.
    NotTaken,
}

/// The comparison + two-way branch that admits one basic block.
#[derive(Debug)]
struct BlockGuard {
    /// The `icmp` condition code as CLIF spells it, e.g. `ult`.
    cc: String,
    /// The comparison's left operand, alias-resolved.
    lhs: String,
    /// The comparison's right operand when it is an integer constant.
    rhs_const: Option<i64>,
    /// Which arm of the branch the guarded block sits on.
    arm: BrifArm,
}

/// One `atomic_rmw` recovered from CLIF text together with the guard admitting
/// the block it sits in.
#[derive(Debug)]
struct GuardedRmw {
    /// `add` or `sub`.
    op: String,
    /// The heap pointer whose RC header the op targets — read back THROUGH the
    /// `iadd_imm ptr, RC_OFFSET` address computation and alias-resolved, so the
    /// guard's subject can be compared against the RMW's subject. `None` when
    /// the address was not computed that way (then no guard can be checked
    /// against it, and the cell fails loudly rather than vacuously).
    subject: Option<String>,
    /// `None` when the RMW's block is not entered through exactly one two-way
    /// branch — i.e. the RMW is unguarded straight-line code, or the block has
    /// several predecessors and no single admitting predicate.
    guard: Option<BlockGuard>,
}

/// Strip a trailing `; …` value comment and surrounding whitespace.
fn inst_text(line: &str) -> &str {
    line.split(';').next().unwrap_or("").trim()
}

/// A branch target or block header body: `block4(v1, v2)` → `block4`;
/// a non-block token → `None`.
fn target_label(operand: &str) -> Option<&str> {
    let label = operand.trim().split('(').next()?;
    let n = label.strip_prefix("block")?;
    (!n.is_empty() && n.bytes().all(|b| b.is_ascii_digit())).then_some(label)
}

/// `block7:` / `block1(v2: i64, v3: i64):` → `block7` / `block1`.
fn block_label(line: &str) -> Option<&str> {
    target_label(line.strip_suffix(':')?)
}

/// `brif v12, block4, block5` → `(cond, taken, not_taken)`.
fn brif_parts(term: &str) -> Option<(&str, &str, &str)> {
    let rest = term.strip_prefix("brif ")?;
    let mut parts = rest.split(',').map(str::trim);
    let cond = parts.next()?;
    let taken = target_label(parts.next()?)?;
    let not_taken = target_label(parts.next()?)?;
    Some((cond, taken, not_taken))
}

/// `jump block1(v0)` → `block1`.
fn jump_target(term: &str) -> Option<&str> {
    target_label(term.strip_prefix("jump ")?)
}

/// Walk `clif` and recover every `atomic_rmw` with the predicate and arm that
/// admit its block.
///
/// Deliberately parses the CLIF *text* (the only per-body artifact the probe
/// seam hands back) but keys on control-flow structure — block boundaries,
/// terminator targets, value definitions, value aliases — never on the presence
/// of a substring.
fn collect_guarded_rmws(clif: &str) -> Vec<GuardedRmw> {
    let mut aliases: HashMap<&str, &str> = HashMap::new();
    let mut defs: HashMap<&str, &str> = HashMap::new();
    // (label, instructions) in source order.
    let mut blocks: Vec<(&str, Vec<&str>)> = Vec::new();

    for raw in clif.lines() {
        let line = inst_text(raw);
        if line.is_empty() {
            continue;
        }
        if let Some(label) = block_label(line) {
            blocks.push((label, Vec::new()));
            continue;
        }
        if !line.contains(" = ") {
            // `v10 -> v1`: a value alias, not an instruction.
            if let Some((dst, src)) = line.split_once(" -> ").filter(|(d, _)| d.starts_with('v')) {
                aliases.insert(dst.trim(), src.trim());
                continue;
            }
        } else if let Some((dst, rhs)) = line.split_once(" = ") {
            defs.insert(dst.trim(), rhs.trim());
        }
        if let Some((_, insts)) = blocks.last_mut() {
            insts.push(line);
        }
    }

    let mut found = Vec::new();
    for (label, insts) in &blocks {
        for &inst in insts {
            let Some((_, rhs)) = inst.split_once(" = ") else {
                continue;
            };
            let Some(args) = rhs.trim().strip_prefix("atomic_rmw.i64 ") else {
                continue;
            };
            let Some((op, operands)) = args.split_once(' ') else {
                continue;
            };
            let addr = operands.split(',').next().unwrap_or("").trim();

            let mut into = predecessors(&blocks, label);
            let guard = match (into.len(), into.pop()) {
                (1, Some(Some((cond, arm)))) => {
                    icmp_parts(&defs, &aliases, cond).map(|(cc, lhs, rhs)| BlockGuard {
                        cc: cc.to_string(),
                        lhs: lhs.to_string(),
                        rhs_const: iconst_value(&defs, rhs),
                        arm,
                    })
                }
                _ => None,
            };

            found.push(GuardedRmw {
                op: op.trim().to_string(),
                subject: rc_subject(&defs, &aliases, addr).map(str::to_string),
                guard,
            });
        }
    }
    found
}

/// Follow `vN -> vM` value aliases to the root value name.
fn resolve_alias<'a>(aliases: &HashMap<&'a str, &'a str>, v: &'a str) -> &'a str {
    let mut cur = v;
    // Alias chains are shallow; the bound only fences a malformed dump.
    for _ in 0..16 {
        match aliases.get(cur) {
            Some(next) => cur = next,
            None => break,
        }
    }
    cur
}

/// `iadd_imm.i64 v2, 8` / `iadd_imm v1, 8` → the base pointer, provided the
/// immediate is exactly `HeapHeader::RC_OFFSET`. That is what makes the recovered
/// subject the POINTER the guard must test, not the RC address.
fn rc_subject<'a>(
    defs: &HashMap<&'a str, &'a str>,
    aliases: &HashMap<&'a str, &'a str>,
    addr: &'a str,
) -> Option<&'a str> {
    let rhs = *defs.get(addr)?;
    let args = rhs
        .strip_prefix("iadd_imm.i64 ")
        .or_else(|| rhs.strip_prefix("iadd_imm "))?;
    let (base, imm) = args.split_once(',')?;
    (imm.trim().parse::<i64>().ok()? == i64::from(HeapHeader::RC_OFFSET))
        .then(|| resolve_alias(aliases, base.trim()))
}

/// `icmp.i64 ult v3, v10` / `icmp ult v1, v2` → (cc, alias-resolved lhs, rhs).
fn icmp_parts<'a>(
    defs: &HashMap<&'a str, &'a str>,
    aliases: &HashMap<&'a str, &'a str>,
    cond: &'a str,
) -> Option<(&'a str, &'a str, &'a str)> {
    let rhs = *defs.get(cond)?;
    let args = rhs
        .strip_prefix("icmp.i64 ")
        .or_else(|| rhs.strip_prefix("icmp "))?;
    let (cc, operands) = args.split_once(' ')?;
    let (lhs, right) = operands.split_once(',')?;
    Some((cc.trim(), resolve_alias(aliases, lhs.trim()), right.trim()))
}

/// `iconst.i64 1024` → `1024`; any other definition → `None`.
fn iconst_value<'a>(defs: &HashMap<&'a str, &'a str>, v: &'a str) -> Option<i64> {
    defs.get(v)?
        .strip_prefix("iconst.i64 ")?
        .trim()
        .parse()
        .ok()
}

/// Every terminator that targets `label`, with the arm it targets it on. `None`
/// entries are unconditional `jump` predecessors — a block reached that way is
/// admitted by no predicate at all.
fn predecessors<'a>(
    blocks: &[(&'a str, Vec<&'a str>)],
    label: &str,
) -> Vec<Option<(&'a str, BrifArm)>> {
    blocks
        .iter()
        .filter_map(|(_, insts)| {
            let term = *insts.last()?;
            if let Some((cond, taken, not_taken)) = brif_parts(term) {
                if taken == label {
                    return Some(Some((cond, BrifArm::Taken)));
                }
                if not_taken == label {
                    return Some(Some((cond, BrifArm::NotTaken)));
                }
                None
            } else if jump_target(term) == Some(label) {
                Some(None)
            } else {
                None
            }
        })
        .collect()
}

/// The load-bearing "same predicate / no polarity gap" half of invariant I-CT
/// (`transitive-drop-glue.md` §4.1), asserted as CONTROL FLOW.
///
/// For every `atomic_rmw` in `clif` — `per_op` of each of `add` and `sub` —
/// the op's block must be entered on the condition-FALSE arm of a `brif` whose
/// condition is `icmp ult <p>, NULLARY_TAG_THRESHOLD`, where `<p>` is the very
/// pointer whose RC header the op targets. So both halves execute **iff
/// `p >= NULLARY_TAG_THRESHOLD`** and are skipped below it: one comparison, one
/// polarity, one guarded path — and the inc's and the dec's subject sets are
/// asserted equal, so they skip the SAME words.
///
/// This is what counting `iconst.i64 1024` occurrences could not see (FIXME
/// 0905). Inverting the dec-side comparison to `uge` releases bare nullary tags
/// and skips real pointers — breaking I-CT in exactly the polarity-gap
/// direction — while leaving the constant count at exactly `fields * 2`.
fn assert_threshold_guarded_rmws(clif: &str, per_op: usize, what: &str) {
    let rmws = collect_guarded_rmws(clif);
    let threshold = i64::try_from(NULLARY_TAG_THRESHOLD).expect("threshold fits i64");
    let mut subjects_by_op: HashMap<&str, Vec<String>> = HashMap::new();

    for op in ["add", "sub"] {
        let of_op: Vec<&GuardedRmw> = rmws.iter().filter(|r| r.op == op).collect();
        assert_eq!(
            of_op.len(),
            per_op,
            "{what}: expected {per_op} `atomic_rmw {op}` op(s), found {}\n{clif}",
            of_op.len()
        );
        for r in of_op {
            let subject = r.subject.as_deref().unwrap_or_else(|| {
                panic!(
                    "{what}: the `{op}` RMW's address is not `iadd_imm ptr, RC_OFFSET`, so no \
                     pointer can be matched against its guard\n{clif}"
                )
            });
            let guard = r.guard.as_ref().unwrap_or_else(|| {
                panic!(
                    "{what}: the `{op}` RMW on {subject} is not admitted by a single two-way \
                     branch — an unguarded RC op dereferences a bare nullary tag\n{clif}"
                )
            });
            assert_eq!(
                guard.cc, "ult",
                "{what}: the `{op}` guard compares with `{}`, not `ult`; the two halves must \
                 share ONE comparison, and `uge` inverts which words are treated as \
                 pointers\n{clif}",
                guard.cc
            );
            assert_eq!(
                guard.lhs, subject,
                "{what}: the `{op}` guard tests {} but the RMW targets {subject}'s RC header — \
                 the threshold constant guards an unrelated value\n{clif}",
                guard.lhs
            );
            assert_eq!(
                guard.rhs_const,
                Some(threshold),
                "{what}: the `{op}` guard's threshold operand is not \
                 NULLARY_TAG_THRESHOLD ({threshold})\n{clif}"
            );
            assert_eq!(
                guard.arm,
                BrifArm::NotTaken,
                "{what}: the `{op}` RMW sits on the condition-TRUE arm of `{} < {threshold}`, so \
                 it executes on bare nullary tags and is SKIPPED for real pointers — the \
                 polarity is inverted\n{clif}",
                guard.lhs
            );
            subjects_by_op.entry(op).or_default().push(subject.to_string());
        }
    }

    for subjects in subjects_by_op.values_mut() {
        subjects.sort();
    }
    assert_eq!(
        subjects_by_op.get("add"),
        subjects_by_op.get("sub"),
        "{what}: the inc and the dec must fire on the SAME words; they name different \
         pointers\n{clif}"
    );
}

/// The shared assertion for both template shapes of §10 row 4's positive cell:
/// ONE guarded inc, ONE balancing guarded dec, both behind the SAME
/// nullary-threshold predicate, and no drop-glue call (there is no concrete type
/// to derive one from — that is the whole point of the admission).
fn assert_balanced_guarded_pair(clif: &str, fields: usize, what: &str) {
    assert_eq!(
        count(clif, "atomic_rmw.i64 add"),
        fields,
        "{what}: the consuming inc must fire once per heap-classified field \
         parameter — it is the half the scope-exit dec balances\n{clif}"
    );
    assert_eq!(
        count(clif, "atomic_rmw.i64 sub"),
        fields,
        "{what}: exactly one balancing shallow dec per field parameter (I-CT); \
         more is a double-release, fewer is the leak direction\n{clif}"
    );
    assert_eq!(
        count_release_ops(clif),
        fields,
        "{what}: the shallow decs are the ONLY releases — a canonical `drop<T>` \
         call here would mean a concrete type was invented for a non-concrete \
         parameter\n{clif}"
    );
    // The inc and the dec must share ONE runtime predicate, on the SAME words,
    // with the SAME polarity — asserted structurally, never by counting
    // threshold constants (FIXME 0905).
    assert_threshold_guarded_rmws(clif, fields, what);
}

// spec: spec/05-definitions.md §5.3 (deftype); appendix-c-nfr §C.1.4 —
// `transitive-drop-glue.md` §4.1 / §10 row 4 POSITIVE: the generic template
// `(deftype (Option a) (Some [:a v]))`. The field parameter's signature type is
// the declared type variable, so no `ConcreteType` exists for it; the guarded
// consuming inc and the balancing guarded scope-exit dec are emitted on the same
// word, behind the same nullary predicate.
#[test]
fn a_generic_ctor_template_balances_its_guarded_inc_with_a_guarded_dec() {
    let (defn, tables) = ctor_template("Option", "Some", &[("v", Type::Var(0))]);
    let clif = compile(&defn, &tables).expect("the generic ctor template must compile");
    assert_balanced_guarded_pair(&clif, 1, "generic ctor template");
}

// spec: spec/05-definitions.md §5.3 (deftype); appendix-c-nfr §C.1.4 —
// `transitive-drop-glue.md` §4.1 / §10 row 4 POSITIVE: the undeclared-field
// template `(deftype B (Mk [v]))`. `B` is monomorphic and no instantiation ever
// pins the field, so typecheck leaves it a free type variable. The class is
// intrinsic to compiling a ctor `Def` ONCE per declaration — not to generics —
// which is why this shape must take the identical path.
#[test]
fn an_undeclared_field_ctor_template_takes_the_same_admission() {
    let (defn, tables) = ctor_template("B", "Mk", &[("v", Type::Var(7))]);
    let clif = compile(&defn, &tables).expect("the undeclared-field template must compile");
    assert_balanced_guarded_pair(&clif, 1, "undeclared-field ctor template");
}

// spec: spec/05-definitions.md §5.3 (deftype); appendix-c-nfr §C.1.4 —
// `transitive-drop-glue.md` §10 row 4 EDGE: a multi-field template incs and decs
// EVERY field parameter. The admission is per-binding, not per-frame-once.
#[test]
fn a_multi_field_template_incs_and_decs_every_field_parameter() {
    let (defn, tables) = ctor_template(
        "Pair",
        "MkPair",
        &[("a", Type::Var(0)), ("b", Type::Var(1))],
    );
    let clif = compile(&defn, &tables).expect("the multi-field template must compile");
    assert_balanced_guarded_pair(&clif, 2, "multi-field ctor template");
}

// spec: spec/05-definitions.md §5.3 (deftype); appendix-c-nfr §C.1.4 —
// `transitive-drop-glue.md` §10 row 4 EDGE: a CONCRETE-field template takes the
// ordinary `drop<T>` path, no exception. Being a ctor template is necessary for
// the admission, never sufficient — the binding must also fail
// `ConcreteType::from_type`.
//
// The design row spells this shape `(deftype B (Mk [:Int v]))`; `Int` is
// `NeverHeap`, so it never reaches a release seam at all and cannot show which
// path was taken. A concrete HEAP field is the observing form of the same claim:
// an unguarded inc (String is `AlwaysHeap`, no nullary tags in its domain) and
// ONE canonical glue call, with no inline shallow dec anywhere.
#[test]
fn a_concrete_heap_field_template_takes_the_ordinary_drop_glue_path() {
    let (defn, tables) = ctor_template("Box", "MkBox", &[("s", Type::String)]);
    let clif = compile(&defn, &tables).expect("the concrete-field template must compile");
    assert_eq!(
        count(&clif, "atomic_rmw.i64 sub"),
        0,
        "a concrete field must not take the §4.1 shallow dec\n{clif}"
    );
    assert_eq!(
        count_release_ops(&clif),
        1,
        "the concrete field's release is ONE call to the canonical `drop<String>` \
         glue — the ordinary path\n{clif}"
    );
    assert_eq!(
        count(&clif, NULLARY_GUARD),
        0,
        "an `AlwaysHeap` field carries no nullary-tag guard at either half\n{clif}"
    );
}
