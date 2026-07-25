use super::*;

use cranelisp_intrinsics::alloc::{alloc_count, dealloc_count};

// spec: bounded-contexts.md §4a — heap-layout offsets single-sourced from
// HeapHeader (Principle 7). Guards the HIGH-1 remediation (audit
// 2026-06-14): the derived offsets MUST equal the canonical layout and the
// RC offset MUST equal HeapHeader::RC_OFFSET. A future HeapHeader change
// that shifts these breaks this test (and the `const _` asserts) rather
// than silently corrupting the raw heap reads/writes.
#[test]
fn heap_offsets_derive_from_heap_header() {
    // Payload base is the header size; fields are i64-strided past it.
    assert_eq!(PAYLOAD_OFFSET, HeapHeader::SIZE);
    assert_eq!(
        FIELD0_OFFSET,
        HeapHeader::SIZE + core::mem::size_of::<i64>()
    );
    assert_eq!(
        FIELD1_OFFSET,
        HeapHeader::SIZE + 2 * core::mem::size_of::<i64>()
    );
    // Behaviour-preserving: identical to the pre-remediation literals.
    assert_eq!(PAYLOAD_OFFSET, 16);
    assert_eq!(FIELD0_OFFSET, 24);
    assert_eq!(FIELD1_OFFSET, 32);
    // shallow_rc_inc writes the RC field at HeapHeader::RC_OFFSET (was a
    // magic `.add(8)`); pin it to the canonical RC location.
    assert_eq!(HeapHeader::RC_OFFSET as usize, 8);
}

// spec: design/arch/CLAUDE.md Decision 24 — shallow_rc_inc increments the
// RC field the marshal bodies share. Behaviour-preserving guard for the
// HIGH-1 single-source change: an inc at the derived RC offset is observed
// by consume_shallow (which reads the same canonical offset).
#[test]
fn shallow_rc_inc_targets_canonical_rc_field() {
    let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
    let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();
    // Fresh heap cell, rc=1.
    let base = alloc_adt_2(TAG_SEXP_INT, 7);
    // Inc via the marshal helper (rc 1 -> 2).
    shallow_rc_inc(base);
    // First consume: rc 2 -> 1, NOT freed (the inc landed at the RC field).
    cranelisp_intrinsics::drop::consume_sexp(base);
    assert_eq!(
        cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before,
        0,
        "inc must land on the RC field so the first dec does not free"
    );
    // Second consume: rc 1 -> 0, freed.
    cranelisp_intrinsics::drop::consume_sexp(base);
    assert_eq!(
        cranelisp_intrinsics::alloc::alloc_count() - allocs_before,
        1
    );
    assert_eq!(
        cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before,
        1,
        "value freed only after the inc'd reference is also released"
    );
}

#[test]
fn test_sconcat_empty_empty() {
    let result = sconcat(TAG_SNIL, TAG_SNIL);
    assert_eq!(result, TAG_SNIL);
}

#[test]
fn test_sconcat_empty_nonempty() {
    let ys = alloc_adt_3(TAG_SCONS, 42, TAG_SNIL);
    let result = sconcat(TAG_SNIL, ys);
    // Result should be ys (since xs is empty).
    let items = unsafe { read_slist(result) };
    assert_eq!(items, vec![42]);
}

#[test]
fn test_sconcat_nonempty_empty() {
    let xs = alloc_adt_3(TAG_SCONS, 1, alloc_adt_3(TAG_SCONS, 2, TAG_SNIL));
    let result = sconcat(xs, TAG_SNIL);
    let items = unsafe { read_slist(result) };
    assert_eq!(items, vec![1, 2]);
}

#[test]
fn test_sconcat_both_nonempty() {
    let xs = alloc_adt_3(TAG_SCONS, 1, alloc_adt_3(TAG_SCONS, 2, TAG_SNIL));
    let ys = alloc_adt_3(TAG_SCONS, 3, TAG_SNIL);
    let result = sconcat(xs, ys);
    let items = unsafe { read_slist(result) };
    assert_eq!(items, vec![1, 2, 3]);
}

// ---------------------------------------------------------------------
// Decision 24 extern-consumption tests (Sprint 56 Step 2c)
//
// `sconcat` incs items of xs into new SCons nodes, takes ONE inc on ys so
// the result can splice it as a tail (RE-1), then releases the original xs
// and ys via `consume_slist`. The test verifies RC balance: after the caller
// drops the result (also via consume_slist), no leaks or double-frees.
//
// NOTE (S118 W2b, §2.2): this row's `ys` is a ONE-cell list of BARE NULLARY
// TAGS, so it sits exactly on the point where the pre-fix deep walk's surplus
// `(n − 1) + h` was zero. It is retained as the arithmetic-invariance pin;
// the `re1_*` rows below are the ones that see the embed rule.
// ---------------------------------------------------------------------

// spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern sconcat
#[test]
fn decision24_sconcat_rc_balanced() {
    let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
    let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();

    // xs = SCons(1, SCons(2, SNil))  — 2 SCons allocs, items are bare tags.
    // ys = SCons(3, SNil)            — 1 SCons alloc.
    let xs = alloc_adt_3(TAG_SCONS, 1, alloc_adt_3(TAG_SCONS, 2, TAG_SNIL));
    let ys = alloc_adt_3(TAG_SCONS, 3, TAG_SNIL);

    // sconcat:
    //   - shallow_rc_inc(ys): the single embed inc — ys SCons rc 1→2.
    //   - builds 2 new SCons nodes holding items 1, 2 (bare tags —
    //     shallow_rc_inc no-op), tail chained to ys.
    //   - consume_slist(xs): last ref → frees both xs SCons nodes.
    //   - consume_slist(ys): rc 2→1, not freed.
    let result = sconcat(xs, ys);
    let items = unsafe { read_slist(result) };
    assert_eq!(items, vec![1, 2, 3]);

    // Caller releases the result (Decision 24 semantics — receiver owns).
    // consume_slist walks: frees the 2 new SCons, then ys SCons (rc 1→0).
    consume_slist(result);

    // allocs: 3 original (xs:2 + ys:1) + 2 new result SCons = 5
    // deallocs: same 5 — no leaks, no double-frees.
    assert_eq!(
        cranelisp_intrinsics::alloc::alloc_count() - allocs_before,
        5,
        "alloc count mismatch"
    );
    assert_eq!(
        cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before,
        5,
        "dealloc count mismatch (leak or double-free)"
    );
}

// =====================================================================
// RE-1 — the structural-embedding ownership contract
// (`design/runtime/s118-structural-embedding-ownership.md` §2, §5)
//
// > **RE-1.** When a runtime helper embeds an existing heap structure into
// > a new structure BY POINTER (structural sharing, not copying), it takes
// > exactly ONE `rc_inc` — on the node it stores — and no others. Interior
// > nodes are owned by their parent node; elements are owned by the node
// > that holds them. Those owners are unchanged by the embedding and MUST
// > NOT be re-counted.
// >
// > *Corollary (the auditable form):* the number of incs a producer
// > performs for one embed is 1, INDEPENDENT of the size and depth of the
// > embedded structure.
//
// Why `decision24_sconcat_rc_balanced` above is green and yet blind (§2.2):
// its `ys` is a ONE-cell list of BARE NULLARY TAGS, and the surplus is
// `over-incs = (n − 1) interior nodes + h heap-typed elements` = `0 + 0`.
// The seam's only pre-S118 row sat exactly on the one point where the
// defect is invisible. The rows below restore both missing axes — `|ys| ≥ 2`
// and heap-typed elements — plus the rate and inc-count fences.
// =====================================================================

/// Read the RC word of a heap value through the canonical header offset.
///
/// # Safety
///
/// `ptr` MUST be a **live, not-yet-released base pointer** produced by this
/// module's allocators (`alloc_adt_2` / `alloc_adt_3` / `alloc_string`, i.e.
/// `alloc_with_rc`) and still owned by the caller across the read.
///
/// That is a **caller** property and the reason this is an `unsafe fn`: the
/// `NULLARY_THRESHOLD` assert below establishes neither provenance, liveness,
/// nor shape — *any* `i64` above the threshold clears it. The assert is a
/// tripwire for the one misuse a live value can legitimately be (a bare
/// nullary tag, which carries no header at all), not a proof of validity.
unsafe fn rc_of(ptr: i64) -> i64 {
    assert!(
        ptr >= NULLARY_THRESHOLD,
        "rc_of called on the bare nullary tag {ptr} — it has no header"
    );
    // SAFETY: the caller guarantees `ptr` is a live `alloc_with_rc` base, so
    // `RC_OFFSET` (8) is inside the header every such allocation carries.
    unsafe { read_i64(ptr, HeapHeader::RC_OFFSET as usize) }
}

/// An SList of `n` cells whose elements are HEAP-typed — each a `SexpSym`
/// owning a heap `String`, so both missing axes of §2.2 (`|ys| ≥ 2` and
/// `h > 0`) are exercised at once.
fn heap_slist(n: usize) -> i64 {
    let items: Vec<i64> = (0..n).map(|i| make_sexp_sym(&format!("e{i}"))).collect();
    build_runtime_list(&items)
}

/// Every SCons node and every heap-typed element of an SList, head first —
/// the complete set of reference holders RE-1 says an embed must not touch
/// beyond the head.
///
/// # Safety
///
/// `ptr` MUST be a **live, well-formed SList**: either `TAG_SNIL` (or another
/// bare nullary tag) or a not-yet-released three-slot `TAG_SCONS` base from
/// `alloc_adt_3`, whose tail cell recursively satisfies the same contract and
/// whose whole chain the caller still owns across the walk.
///
/// The loop condition (`ptr >= NULLARY_THRESHOLD`) is a *termination* test, not
/// a validity test: it cannot distinguish an SCons base from any other above-
/// threshold `i64`, so provenance, liveness and three-slot shape are the
/// caller's to guarantee — hence `unsafe fn`. The returned element pointers
/// inherit that guarantee and are only as valid as the chain they were read
/// from.
unsafe fn nodes_and_elements(mut ptr: i64) -> (Vec<i64>, Vec<i64>) {
    let (mut nodes, mut elements) = (Vec::new(), Vec::new());
    while ptr >= NULLARY_THRESHOLD {
        nodes.push(ptr);
        // SAFETY: the caller guarantees `ptr` is a live three-slot SCons base,
        // so both field offsets are inside its payload.
        let head = unsafe { read_i64(ptr, FIELD0_OFFSET) };
        if head >= NULLARY_THRESHOLD {
            elements.push(head);
        }
        // SAFETY: as above — `FIELD1_OFFSET` is the same node's tail cell, and
        // the caller's contract extends to the chain it points at.
        ptr = unsafe { read_i64(ptr, FIELD1_OFFSET) };
    }
    (nodes, elements)
}

/// `allocs − deallocs` across one full `sconcat`-and-release cycle: build a
/// one-cell heap-typed `xs`, build `ys` from `build_ys`, concatenate,
/// release the result. Zero is the contract; a positive value is exactly the
/// undischargeable surplus RE-1 forbids.
fn sconcat_residual(build_ys: impl FnOnce() -> i64) -> isize {
    let a0 = alloc_count();
    let d0 = dealloc_count();
    let xs = build_runtime_list(&[make_sexp_sym("x")]);
    let ys = build_ys();
    let result = sconcat(xs, ys);
    consume_slist(result);
    (alloc_count() - a0) as isize - (dealloc_count() - d0) as isize
}

// spec: design/runtime/s118-structural-embedding-ownership.md §2 RE-1 —
// `decision24_sconcat_rc_balanced` widened off its blind point (§2.2): a
// TWO-cell `ys` (one interior node) whose elements are HEAP-typed. The
// deleted `deep_rc_inc_slist` performed `n + h = 4` incs where RE-1 licenses
// one, and tree-ownership `consume_slist` cannot discharge the surplus.
#[test]
fn re1_sconcat_heap_typed_two_cell_tail_balances_exactly() {
    let a0 = alloc_count();
    let d0 = dealloc_count();

    let xs = build_runtime_list(&[make_sexp_sym("x")]);
    let ys = heap_slist(2);
    let result = sconcat(xs, ys);

    // Value half first: the contract is the right list, then exact balance.
    // SAFETY: `result` is the SList `sconcat` just returned.
    let items = unsafe { read_slist(result) };
    assert_eq!(items.len(), 3, "xs ++ ys must have |xs| + |ys| items");

    consume_slist(result);

    let allocs = alloc_count() - a0;
    let deallocs = dealloc_count() - d0;
    assert_eq!(
        allocs,
        deallocs,
        "RE-1: embedding a 2-cell heap-typed tail must leave nothing behind; \
         allocs={allocs} deallocs={deallocs} residual={}. A deep inc mints \
         (n−1) interior-node + h element references no structural owner holds.",
        allocs as isize - deallocs as isize
    );
}

// spec: design/runtime/s118-structural-embedding-ownership.md §2 RE-1
// corollary — the RATE property, the unit-tier twin of e2e repro B4. The
// residual must be zero AND independent of `|ys|`: a fix that trimmed a
// constant surplus while leaving a per-node one would pass a single size.
#[test]
fn re1_sconcat_residual_is_zero_and_independent_of_tail_length() {
    let r1 = sconcat_residual(|| heap_slist(1));
    let r4 = sconcat_residual(|| heap_slist(4));
    let r8 = sconcat_residual(|| heap_slist(8));
    assert_eq!(
        (r1, r4, r8),
        (0, 0, 0),
        "RE-1 corollary: one embed leaks nothing at any tail length; got \
         |ys|=1 -> {r1}, |ys|=4 -> {r4}, |ys|=8 -> {r8}. A residual that GROWS \
         with |ys| is the deep-walk signature (`(n−1) + h`)."
    );
}

// spec: design/runtime/s118-structural-embedding-ownership.md §2 RE-1 /
// RE-3 — the DEPTH axis of the same corollary. A `ys` element that is itself
// a nested structure (`SexpList` holding an `SList`) must not move the inc
// count either: the element is owned by the node holding it, whatever it
// contains.
#[test]
fn re1_sconcat_residual_does_not_move_with_element_depth() {
    let flat = sconcat_residual(|| heap_slist(2));
    let nested = sconcat_residual(|| {
        let inner = build_runtime_list(&[make_sexp_sym("a"), make_sexp_sym("b")]);
        let deep = alloc_adt_2(TAG_SEXP_LIST, inner);
        build_runtime_list(&[deep, make_sexp_sym("c")])
    });
    assert_eq!(
        (flat, nested),
        (0, 0),
        "RE-1: the embed's reference count is a property of the EMBED, not of \
         what the embedded structure contains; flat -> {flat}, nested -> {nested}"
    );
}

// spec: design/runtime/s118-structural-embedding-ownership.md §5 — the
// NET-DELTA half of the inc-count fence, asserted against the reference counts
// themselves rather than by inspection, so a deep-inc regression fails here
// even if some future accounting change re-balanced the totals.
//
// Across one `sconcat` call the whole of `ys` must see a NET RC delta of
// zero at every node and every element: the head takes the single embed inc
// (RE-1) and gives it straight back to the Decision-24 `consume_slist(ys)`
// epilogue, and nothing else in the structure is touched at all. The summed
// delta is size-independent by construction — under the deep walk it is
// `(n + h) − 1`, which GROWS with `|ys|`.
//
// SCOPE (FIXME 0885): this row proves interior holders were UNTOUCHED and that
// the surplus does not scale with `|ys|`. It cannot see the difference between
// "one inc paired with one consume" and "neither" — both net to zero — so it
// does NOT pin the §3 ruling that the pair stays unconditional and explicit.
// That is the GROSS-TALLY half's job:
// `re1_embed_inc_tally_is_one_per_call_plus_one_per_copied_item` below.
#[test]
fn re1_embed_takes_exactly_one_reference_whatever_the_tail_size() {
    for n in [1usize, 2, 4, 8] {
        let a0 = alloc_count();
        let d0 = dealloc_count();

        let xs = build_runtime_list(&[make_sexp_sym("x")]);
        let ys = heap_slist(n);
        // SAFETY: `ys` is the well-formed SList `heap_slist` just built and this
        // test still owns; nothing has released it.
        let (nodes, elements) = unsafe { nodes_and_elements(ys) };
        // SAFETY: every pointer here was just read out of that live chain — the
        // nodes are its SCons bases, the elements its heap-typed heads — and the
        // chain is still owned, so each is a live `alloc_with_rc` base.
        let before: Vec<i64> = nodes
            .iter()
            .chain(&elements)
            .map(|p| unsafe { rc_of(*p) })
            .collect();

        let result = sconcat(xs, ys);

        // SAFETY: the same live pointers. `sconcat` took a reference on the
        // embedded head and released only the references it was handed, so the
        // whole of `ys` is still owned here — through `result`, which this test
        // has not released yet.
        let after: Vec<i64> = nodes
            .iter()
            .chain(&elements)
            .map(|p| unsafe { rc_of(*p) })
            .collect();
        let deltas: Vec<i64> = before.iter().zip(&after).map(|(b, a)| a - b).collect();
        let summed: i64 = deltas.iter().sum();
        assert_eq!(
            summed,
            0,
            "RE-1 inc-count fence at |ys|={n}: one embed = exactly one inc on \
             the stored node, paired with the Decision-24 consume, so the net \
             RC delta over the whole tail is 0. Got per-holder deltas {deltas:?} \
             (nodes {} then elements {}), summing to {summed}. A summed delta \
             that scales with |ys| is a producer minting references no owner \
             holds.",
            nodes.len(),
            elements.len()
        );

        consume_slist(result);
        assert_eq!(
            alloc_count() - a0,
            dealloc_count() - d0,
            "|ys|={n}: the cycle must also balance"
        );
    }
}

// =====================================================================
// The GROSS inc tally (FIXME 0885) — the structural pin for the §3 ruling
// =====================================================================
//
// WHY A SECOND FENCE. The net-delta row above proves the RC words of `ys` come
// back where they started. It is blind to the §3-REJECTED "move instead of
// inc-then-consume" variant (delete BOTH `shallow_rc_inc(ys)` and
// `consume_slist(ys)`), because deleting a +1 and a −1 leaves every net delta
// exactly as it was — and that variant also passes every balance row and the
// shared-tail row. So the ruling that the pair stays UNCONDITIONAL and EXPLICIT
// (Principle 18 — enforce invariants structurally; Principle 26) had no fence.
//
// WHAT THIS ROW ADDS. The RC-stats `rc_inc` tally counts RC operations, not net
// effect, so it separates "one inc plus one consume" from "neither". The
// arithmetic pins BOTH terms of RE-1's licensed count independently:
//
//     tally(one sconcat call) = |xs items copied| + 1 embed
//
// Two scenario children run the SAME four-size tail matrix and differ only in
// `|xs|` (1 vs 3), against a control child that builds and releases identical
// fixtures without concatenating. With `C = TALLY_TAIL_SIZES.len()` calls:
//
//     D1 = C × (1 + e)        D3 = C × (3 + e)
//
// so `(D3 − D1) / (2C) = 1` is the per-copied-item rate and `D1/C − 1 = e` is
// the per-CALL embed constant. Two equations, two unknowns, both forced to 1.
//
// WHY THIS EXCLUDES THE MOVE VARIANT. Deleting the embed inc sets `e = 0`, so
// the expected pair `(D1, D3) = (8, 16)` becomes `(4, 12)` and both halves of
// the assertion fail. The exclusion argument has to live in this comment and in
// the arithmetic rather than in a committed red row: the rejected variant is a
// DELETION of shipped code, so it cannot be committed alongside the fix. What
// is committed is an assertion whose expected values are derived from the
// mechanism (`e = 1`), not observed from the implementation — `e` appears as a
// named constant below precisely so the derivation is auditable.
//
// WHY SUBPROCESSES. The `rc_inc` tally is a process-global counter gated on
// `CRANELISP_RC_STATS`, published only by the at-exit `[RC_STATS]` line. Arming
// is child-`Command` + `env_clear` ONLY — never `set_var` (a `LazyLock` already
// forced makes `set_var` a no-op that merely LOOKS armed; the standing gate is
// `tests/detector_arming_discipline_guard.rs`), and never suite-global. The
// three child bodies are ordinary non-`#[ignore]`d tests that assert their own
// alloc/dealloc balance, so the normal suite executes all of them unarmed on
// every run; only the parent reads their tallies.

/// The tail sizes every tally child sweeps. `|ys|` must not move the count.
const TALLY_TAIL_SIZES: [usize; 4] = [1, 2, 4, 8];

/// The embed constant RE-1 licenses: ONE reference per structural embed,
/// whatever the size and depth of the embedded structure. Derived from the
/// contract, not from the implementation — it is what this row asserts.
const EMBED_INCS_PER_CALL: i64 = 1;

/// One real `rc_inc`, paired with its release. Every tally child runs this
/// first: `rc_stats_enabled()` (and with it the at-exit `[RC_STATS]` printer)
/// is only forced by the first above-threshold `rc_inc`, so without it the
/// control child — which performs no incs of its own — would print no line at
/// all. It contributes exactly 1 to every child and cancels in the differences.
fn arm_rc_stats_printer() {
    let cell = alloc_adt_2(TAG_SEXP_INT, 0);
    shallow_rc_inc(cell);
    consume_sexp(cell);
    consume_sexp(cell);
}

/// The fixture set every tally child builds, identically, for one tail size: a
/// one-item `xs`, a three-item `xs`, and a tail of size `n` for each. Building
/// and releasing an SList performs no RC incs; making the fixtures common
/// anyway means anything that is NOT `sconcat`'s inc traffic is identical
/// across the three children and cancels in the parent's differences.
fn tally_fixtures(n: usize) -> (i64, i64, i64, i64) {
    (heap_slist(1), heap_slist(3), heap_slist(n), heap_slist(n))
}

/// CONTROL child: builds the fixtures, concatenates NOTHING, releases both
/// pairs directly. Its tally is the process floor the scenarios subtract.
#[test]
fn re1_tally_child_control() {
    let (a0, d0) = (alloc_count(), dealloc_count());
    arm_rc_stats_printer();
    for n in TALLY_TAIL_SIZES {
        let (xs1, xs3, ys_a, ys_b) = tally_fixtures(n);
        consume_slist(xs1);
        consume_slist(ys_a);
        consume_slist(xs3);
        consume_slist(ys_b);
    }
    assert_eq!(
        alloc_count() - a0,
        dealloc_count() - d0,
        "the tally control child must balance"
    );
}

/// SCENARIO child, `|xs| = 1`: one `sconcat` per tail size; the three-item
/// fixture is released directly so the allocation work matches the control.
#[test]
fn re1_tally_child_xs1() {
    let (a0, d0) = (alloc_count(), dealloc_count());
    arm_rc_stats_printer();
    for n in TALLY_TAIL_SIZES {
        let (xs1, xs3, ys_a, ys_b) = tally_fixtures(n);
        consume_slist(sconcat(xs1, ys_a));
        consume_slist(xs3);
        consume_slist(ys_b);
    }
    assert_eq!(
        alloc_count() - a0,
        dealloc_count() - d0,
        "the |xs|=1 tally child must balance"
    );
}

/// SCENARIO child, `|xs| = 3`: the same shape with the other fixture pair
/// routed through `sconcat`, isolating the per-copied-item term.
#[test]
fn re1_tally_child_xs3() {
    let (a0, d0) = (alloc_count(), dealloc_count());
    arm_rc_stats_printer();
    for n in TALLY_TAIL_SIZES {
        let (xs1, xs3, ys_a, ys_b) = tally_fixtures(n);
        consume_slist(sconcat(xs3, ys_b));
        consume_slist(xs1);
        consume_slist(ys_a);
    }
    assert_eq!(
        alloc_count() - a0,
        dealloc_count() - d0,
        "the |xs|=3 tally child must balance"
    );
}

/// The libtest name of a child body in this binary (`module::path::fn`, with
/// the crate name stripped — libtest names are crate-root-relative).
fn tally_child_path(name: &str) -> String {
    let m = module_path!();
    let m = m.split_once("::").map(|(_, rest)| rest).unwrap_or(m);
    format!("{m}::{name}")
}

/// Run ONE child body in a fresh process with the RC-stats tally armed, and
/// return its at-exit `rc_inc` count. `env_clear` + an enumerated allow-list:
/// the arming reaches this child and nothing else, and no ambient `CRANELISP_*`
/// is inherited.
fn rc_inc_tally_of_child(child: &str) -> i64 {
    let exe = std::env::current_exe().expect("current_exe for the RC-stats tally child");
    let mut cmd = std::process::Command::new(&exe);
    cmd.env_clear();
    // The one inherited value: the dynamic-loader path this binary may need.
    if let Some(p) = std::env::var_os("LD_LIBRARY_PATH") {
        cmd.env("LD_LIBRARY_PATH", p);
    }
    cmd.env("CRANELISP_RC_STATS", "1");
    cmd.args([&tally_child_path(child), "--exact", "--nocapture"]);
    let out = cmd.output().expect("spawn the RC-stats tally child");
    let mut text = String::from_utf8_lossy(&out.stderr).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stdout));
    assert!(
        out.status.success(),
        "[{child}] the tally child must exit normally:\n{text}"
    );
    let line = text
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("[{child}] no [RC_STATS] line in child output:\n{text}"));
    let tok = line
        .split_whitespace()
        .find_map(|t| t.strip_prefix("rc_inc="))
        .unwrap_or_else(|| panic!("[{child}] [RC_STATS] line carries no rc_inc field: {line}"));
    tok.parse()
        .unwrap_or_else(|e| panic!("[{child}] rc_inc={tok:?} is not an integer: {e}"))
}

// spec: design/runtime/s118-structural-embedding-ownership.md §3 (the
// unconditional inc/consume ruling; "move instead of inc-then-consume" listed
// under Rejected mechanism alternatives) + §5 — the GROSS-TALLY half of the
// inc-count fence. See the block comment above for the derivation and for why
// the move-variant exclusion argument lives in the arithmetic.
#[test]
fn re1_embed_inc_tally_is_one_per_call_plus_one_per_copied_item() {
    let control = rc_inc_tally_of_child("re1_tally_child_control");
    let one_item = rc_inc_tally_of_child("re1_tally_child_xs1");
    let three_items = rc_inc_tally_of_child("re1_tally_child_xs3");

    let calls = TALLY_TAIL_SIZES.len() as i64;
    let (d1, d3) = (one_item - control, three_items - control);
    let (want1, want3) = (
        calls * (1 + EMBED_INCS_PER_CALL),
        calls * (3 + EMBED_INCS_PER_CALL),
    );
    assert_eq!(
        (d1, d3),
        (want1, want3),
        "RE-1 gross inc tally over {calls} `sconcat` calls (tail sizes \
         {TALLY_TAIL_SIZES:?}): each call must perform exactly |xs| copy incs \
         plus {EMBED_INCS_PER_CALL} embed inc, independent of |ys|. Expected \
         |xs|=1 -> {want1} and |xs|=3 -> {want3}; got {d1} and {d3} (raw \
         tallies control={control} xs1={one_item} xs3={three_items}).\n\
         \x20 - Both LOW by {calls} (i.e. {}, {}): the embed inc is gone. If the \
         `consume_slist(ys)` epilogue went with it the totals still balance and \
         every other RE-1 row stays green — that is the §3-REJECTED move variant, \
         and this row is its only fence (Principle 18).\n\
         \x20 - Growing with |ys|: a deep walk has returned (RE-1 corollary).",
        want1 - calls * EMBED_INCS_PER_CALL,
        want3 - calls * EMBED_INCS_PER_CALL
    );
}

// spec: design/runtime/s118-structural-embedding-ownership.md §5 (shared
// tail) — the case the head inc is LOAD-BEARING for, and the fence against
// the rejected deep-consume fix. The caller still holds `ys` after the call
// (Decision 24: heap-typed Var args are inc'd at the call site), so releasing
// the result must NOT tear the tail down; the two releases together balance.
#[test]
fn re1_shared_tail_survives_the_results_release() {
    let a0 = alloc_count();
    let d0 = dealloc_count();

    let ys = heap_slist(2);
    // The caller's own reference, plus the one the call consumes.
    shallow_rc_inc(ys);
    let xs = build_runtime_list(&[make_sexp_sym("x")]);
    let result = sconcat(xs, ys);

    consume_slist(result);

    // The caller's binding is still alive and still reads correctly. (A
    // premature free here would be a stale read; under M1 quarantine it is a
    // detector hit, and in this profile the double-free assert in
    // `alloc::dealloc` catches the release below.)
    // SAFETY: `ys` is the caller's own still-owned reference — the test took an
    // extra one with `shallow_rc_inc` before the call, and only the call's
    // reference has been released.
    assert_eq!(
        unsafe { rc_of(ys) },
        1,
        "the tail the caller still holds must survive"
    );
    // SAFETY: `ys` is the caller's still-owned SList.
    let items = unsafe { read_slist(ys) };
    assert_eq!(items.len(), 2, "the shared tail must still read correctly");

    consume_slist(ys);
    let (allocs, deallocs) = (alloc_count() - a0, dealloc_count() - d0);
    assert_eq!(
        allocs, deallocs,
        "both releases together must balance exactly; allocs={allocs} \
         deallocs={deallocs}"
    );
}

// spec: design/runtime/s118-structural-embedding-ownership.md §5 (shared
// tail, edge) — `ys` ALIASES a suffix of `xs`. The items copied out of `xs`
// and the node embedded as the tail are then the same allocation graph; the
// single head inc is what keeps the aliased suffix alive across
// `consume_slist(xs)`.
#[test]
fn re1_tail_aliasing_a_suffix_of_xs_balances_and_reads() {
    let a0 = alloc_count();
    let d0 = dealloc_count();

    let xs = heap_slist(3);
    // SAFETY: `xs` is the well-formed SList `heap_slist` just built and this
    // test still owns; nothing has released it.
    let (nodes, _) = unsafe { nodes_and_elements(xs) };
    let ys = nodes[2]; // the last SCons of xs
    // Passing the suffix as a second owned argument takes its own reference.
    shallow_rc_inc(ys);

    let result = sconcat(xs, ys);
    // SAFETY: `result` is the SList `sconcat` just returned.
    let items = unsafe { read_slist(result) };
    assert_eq!(items.len(), 4, "xs ++ (suffix of xs) = 3 + 1 items");

    consume_slist(result);
    let (allocs, deallocs) = (alloc_count() - a0, dealloc_count() - d0);
    assert_eq!(
        allocs, deallocs,
        "aliased-suffix embed must balance; allocs={allocs} deallocs={deallocs}"
    );
}

// spec: design/runtime/s118-structural-embedding-ownership.md §5 (empty /
// nullary) — the `items.is_empty()` branch (result IS `ys`) and the three
// `SNil` shapes. `shallow_rc_inc` carries the nullary-tag skip, so a `ys` of
// `SNil` must never reach the RC field of a non-existent header.
#[test]
fn re1_empty_and_nullary_shapes_balance() {
    // xs = SNil, ys = heap: the `items.is_empty()` arm.
    let a0 = alloc_count();
    let d0 = dealloc_count();
    let ys = heap_slist(2);
    let result = sconcat(TAG_SNIL, ys);
    assert_eq!(result, ys, "the empty-xs arm returns ys itself");
    consume_slist(result);
    assert_eq!(
        alloc_count() - a0,
        dealloc_count() - d0,
        "empty-xs arm must balance"
    );

    // xs = heap, ys = SNil.
    let a1 = alloc_count();
    let d1 = dealloc_count();
    let xs = heap_slist(2);
    let result = sconcat(xs, TAG_SNIL);
    // SAFETY: `result` is the SList `sconcat` just returned.
    assert_eq!(unsafe { read_slist(result) }.len(), 2);
    consume_slist(result);
    assert_eq!(
        alloc_count() - a1,
        dealloc_count() - d1,
        "empty-ys arm must balance"
    );

    // Both SNil: the heap is not touched at all.
    let a2 = alloc_count();
    let d2 = dealloc_count();
    assert_eq!(sconcat(TAG_SNIL, TAG_SNIL), TAG_SNIL);
    assert_eq!(alloc_count() - a2, 0, "SNil ++ SNil must not allocate");
    assert_eq!(dealloc_count() - d2, 0, "SNil ++ SNil must not free");
}

// spec: design/runtime/s118-structural-embedding-ownership.md §2 RE-3 — the
// sibling producer's per-field choice. `quote_sexp`'s `TAG_SEXP_SYM` /
// `TAG_SEXP_STR` arms DEEP-COPY the wrapper but RE-USE the `String` pointer,
// so they take exactly one inc on the leaf they re-use. Nested `SexpList`
// recursion re-uses nothing and incs nothing.
#[test]
fn re3_quote_sexp_string_reuse_and_nested_list_balance() {
    let a0 = alloc_count();
    let d0 = dealloc_count();
    let sym = make_sexp_sym("hello");
    let quoted = quote_sexp(sym);
    consume_sexp(quoted);
    assert_eq!(
        alloc_count() - a0,
        dealloc_count() - d0,
        "SexpSym quote re-uses the String with ONE inc — balance is exact"
    );

    let a1 = alloc_count();
    let d1 = dealloc_count();
    let inner = build_runtime_list(&[make_sexp_sym("a"), alloc_adt_2(TAG_SEXP_INT, 7)]);
    let nested = alloc_adt_2(TAG_SEXP_LIST, inner);
    let quoted = quote_sexp(nested);
    consume_sexp(quoted);
    assert_eq!(
        alloc_count() - a1,
        dealloc_count() - d1,
        "nested SexpList quote balances exactly"
    );
}

// spec: design/runtime/s118-structural-embedding-ownership.md §5 (negative /
// fence, "grep-zero") — no producer in `marshal.rs` performs an inc whose
// count scales with the size of a structure it embeds. `deep_rc_inc_slist`
// was deleted at S118 W2b and must have no successor: an embed-site inc that
// sits inside a walk over the embedded structure is the defect class, not an
// implementation detail.
#[test]
fn re1_marshal_has_no_size_scaling_embed_inc() {
    let src = include_str!("../marshal.rs");
    assert!(
        !src.contains("deep_rc_inc"),
        "`deep_rc_inc_slist` was deleted at S118 W2b (RE-1); a successor by \
         any name re-introduces the class"
    );
}
