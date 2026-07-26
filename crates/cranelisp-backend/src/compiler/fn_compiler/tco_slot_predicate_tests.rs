//! S118 slice S5 — the ONE TCO replacement/transfer predicate
//! (`design/backend/transitive-drop-glue.md` §6, §10 row 6).
//!
//! [`super::tco_slot_disposition`] is pure over `(facts, analysis_off)`, so the
//! whole verdict table is exercised without a live `FnCompiler`. It replaced
//! four separately-evaluated conditions combined ad hoc inside two
//! `collect_frame_heap_decs` filters; the value of folding them is that the
//! rows can now disagree only here, once, in the open.

use super::{SlotDisposition, TailSlotFacts, tco_slot_disposition};

/// Row 5 — the default: nothing about this slot is carried forward.
fn unrelated() -> TailSlotFacts {
    TailSlotFacts::default()
}

// spec: spec/12-runtime.md §12.3.1 — §6 row 1. A bare local `Var` tail argument
// naming the slot MOVES the old owner into the next iteration; the box carries
// forward and dec'ing it would double-free the value the new iteration owns.
// Same verdict for a same-slot and a cross-slot move: the predicate answers
// about the OWNER's continuity, not about slot positions.
#[test]
fn a_bare_var_move_transfers_the_old_owner() {
    let facts = TailSlotFacts {
        named_by_bare_var_arg: true,
        ..unrelated()
    };
    assert_eq!(
        tco_slot_disposition(facts, false),
        SlotDisposition::TransferOldOwner
    );
    assert_eq!(
        tco_slot_disposition(facts, true),
        SlotDisposition::TransferOldOwner,
        "a move is a move under either ownership toggle — it is structural"
    );
}

// spec: spec/12-runtime.md §12.3.1 — §6 row 5. A fresh constructor/call/literal,
// a copied COW result, an unrelated variable, or unknown provenance is a
// REPLACEMENT: the slot's old value is unreachable after the overwrite and its
// glue must run before it. Unknown is conservative replacement because a
// suppressed release is at worst a leak while a guessed transfer is a UAF.
#[test]
fn an_unrelated_or_unknown_replacement_releases_the_old_slot() {
    assert_eq!(
        tco_slot_disposition(unrelated(), false),
        SlotDisposition::Replace
    );
    assert_eq!(
        tco_slot_disposition(unrelated(), true),
        SlotDisposition::Replace
    );
}

// spec: spec/12-runtime.md §12.3.1 — §6 row 3 with its TOGGLE ASYMMETRY intact
// (FIXME 0695). Analysis-ON, an in-place COW rooted at this slot forwards the
// slot's OWN box, so the slot is not superseded. Under `CRANELISP_NO_OWNERSHIP`
// the source is force-counted so the op ALWAYS copies: nothing is carried
// forward and the dec is always owed. The toggle is an explicit input rather
// than a second site's env read.
#[test]
fn the_inplace_cow_exemption_is_analysis_on_only() {
    let facts = TailSlotFacts {
        inplace_cow_rooted_here: true,
        ..unrelated()
    };
    assert_eq!(
        tco_slot_disposition(facts, false),
        SlotDisposition::TransferOldOwner
    );
    assert_eq!(
        tco_slot_disposition(facts, true),
        SlotDisposition::Replace,
        "toggle-off always copies, so the superseded slot's release is owed \
         (FIXME 0695)"
    );
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE — the F1 REGRESSION FENCE) — §6
// row 2 must NOT become a blanket skip.
//
// A control-flow tail argument (`(recur (if c lo hi))`) carries DISTINCT
// bindings per branch, so a static transfer verdict would retain the dead
// branch's binding and hand the loop param a value the frame no longer
// accounts for — the F1 use-after-free (`ownership-codegen.md` §13.3). The
// established strategy is a per-branch protective inc followed by a UNIFORM
// flush, so a control-flow argument contributes no transfer fact at all: it
// leaves the facts at their default and lands on `Replace`.
//
// This cell is the fence: if a future fold adds a `control_flow_forwards` fact
// that answers `TransferOldOwner`, it fails here.
#[test]
fn a_control_flow_argument_does_not_license_a_blanket_skip_neg() {
    // Everything a control-flow argument can contribute is "not a bare Var and
    // not an in-place COW" — the default facts.
    assert_eq!(
        tco_slot_disposition(unrelated(), false),
        SlotDisposition::Replace,
        "row 2 must stay a REPLACE at the predicate; the protective inc plus \
         uniform flush is the emission strategy, and turning it into a skip \
         re-introduces the F1 UAF"
    );
    // The fact set itself carries no control-flow transfer channel.
    let f = unrelated();
    assert!(!f.named_by_bare_var_arg && !f.inplace_cow_rooted_here);
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE) — §6 row 4: a BORROWED alias
// cannot license a transfer. It carries no independently owned reference, so
// suppressing the slot's release on its strength leaves the carried value with
// no owner at all.
//
// `tail_transfer_skip` is spelling-based — "a literal top-level `Var` argument"
// — and never asked this question, so a borrowed match-field binding SHADOWING
// a frame-owned parameter suppressed a release on the strength of an alias that
// owns nothing. The verdict is loud, not a guessed release and not a silent
// skip: **Narrowing carries its check**.
#[test]
fn a_borrowed_alias_cannot_license_a_transfer_neg() {
    let facts = TailSlotFacts {
        named_by_bare_var_arg: true,
        bare_var_arg_is_borrowed: true,
        ..unrelated()
    };
    assert_eq!(
        tco_slot_disposition(facts, false),
        SlotDisposition::BorrowedInvalid
    );
    assert_eq!(
        tco_slot_disposition(facts, true),
        SlotDisposition::BorrowedInvalid,
        "ownership validity is structural — it does not depend on the toggle"
    );
    // And it is not quietly downgraded to a transfer by a COW fact either.
    let with_cow = TailSlotFacts {
        inplace_cow_rooted_here: true,
        ..facts
    };
    assert_eq!(
        tco_slot_disposition(with_cow, false),
        SlotDisposition::BorrowedInvalid
    );
}
