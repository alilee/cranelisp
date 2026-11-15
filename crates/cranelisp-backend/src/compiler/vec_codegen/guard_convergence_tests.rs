//! S122 Q9 — Vec copies use the canonical nullary-tag guard and polarity.

use std::collections::HashMap;

use cranelisp_types::NULLARY_TAG_THRESHOLD;

use super::*;
use crate::jit::Jit;

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
/// (`transitive-drop-glue.md` §4.1), asserted as CONTROL FLOW. Relocated here
/// from the retired constructor-template cells, its other consumer.
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
fn assert_threshold_guarded_op(clif: &str, op: &str, expected: usize, what: &str) -> Vec<String> {
    let rmws = collect_guarded_rmws(clif);
    let threshold = i64::try_from(NULLARY_TAG_THRESHOLD).expect("threshold fits i64");
    let of_op: Vec<&GuardedRmw> = rmws.iter().filter(|r| r.op == op).collect();
    assert_eq!(
        of_op.len(),
        expected,
        "{what}: expected {expected} `atomic_rmw {op}` op(s), found {}\n{clif}",
        of_op.len()
    );
    let mut subjects = Vec::with_capacity(of_op.len());
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
            "{what}: the `{op}` guard compares with `{}`, not `ult`; the guard must admit \
             only heap pointers\n{clif}",
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
        subjects.push(subject.to_owned());
    }
    subjects.sort();
    subjects
}

fn assert_threshold_guarded_adds(clif: &str, expected: usize, what: &str) {
    let _ = assert_threshold_guarded_op(clif, "add", expected, what);
}

fn elem_adapter_clif(guarded: bool) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));
    let mut fn_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fn_ctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let val = builder.block_params(entry)[0];
    emit_elem_inc_body(&mut builder, module, val, guarded);
    builder.finalize();
    ctx.func.display().to_string()
}

fn mixed_vec_get_clif() -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module = jit.jit_module();
    let mut panic_sig = module.make_signature();
    panic_sig.params.push(AbiParam::new(types::I64));
    panic_sig.params.push(AbiParam::new(types::I64));
    let panic_id = module
        .declare_function("runtime/panic", Linkage::Import, &panic_sig)
        .expect("declare panic import");

    let mut ctx = module.make_context();
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.params.push(AbiParam::new(types::I64));
    ctx.func.signature.returns.push(AbiParam::new(types::I64));
    let mut fn_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fn_ctx);
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let vec_val = builder.block_params(entry)[0];
    let idx_val = builder.block_params(entry)[1];
    let elem = emit_vec_get_core(
        &mut builder,
        module,
        panic_id,
        Some(HeapCategory::Mixed),
        vec_val,
        idx_val,
        Span::SYNTHETIC,
    )
    .expect("emit mixed vec-get");
    builder.ins().return_(&[elem]);
    builder.finalize();
    ctx.func.display().to_string()
}

// spec: design/backend/s122-closure.md §3 — both the generated element-copy
// adapter and an inline Mixed-element Vec read place their RC increment on the
// not-taken arm of `value < NULLARY_TAG_THRESHOLD` through the shared emitter.
#[test]
fn vec_copy_shapes_share_the_canonical_nullary_guard_polarity() {
    let adapter = elem_adapter_clif(true);
    assert_threshold_guarded_adds(&adapter, 1, "mixed Vec element adapter");

    let inline = mixed_vec_get_clif();
    assert_threshold_guarded_adds(&inline, 1, "inline mixed Vec read");
}

// The NeverHeap/AlwaysHeap adapter control remains unguarded.
#[test]
fn always_heap_element_adapter_keeps_the_unguarded_control() {
    let adapter = elem_adapter_clif(false);
    assert_eq!(adapter.matches("atomic_rmw.i64 add").count(), 1);
    assert!(!adapter.contains("icmp.i64 ult"));
}
