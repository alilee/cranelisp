---
number: 0879
target: /design
filed_by: /dev
filed_at: 2026-07-25
sprint_filed: 118
refers_to: design/intrinsics/diagnostic-modes.md §7.5 (seam_precheck predicate (a)) and §5 A2/A4 amendment; crates/cranelisp-intrinsics/src/diagnostics.rs (header_size_plausible)
status: open
---

# §7.5's "8-aligned alloc_size" predicate false-positives on every HeapString

## Issue

§7.5 specifies the shared precheck's predicate (a) as: read the alleged base's
`alloc_size` word and **"reject unless it is `>= HeapHeader::SIZE` **and**
8-aligned"**, and widens `alloc::dealloc`'s A4 predicate "from `total_size <
HeapHeader::SIZE` to `< HeapHeader::SIZE` or not 8-aligned".

Implemented literally, that rejects legitimate live allocations. `HeapString`'s
payload is `size_of::<i64>() + byte_len` **raw bytes**
(`heap_string.rs::payload_size`), so a 3-byte string's `alloc_size` is
`16 + 8 + 3 = 27` — a correct, deliberately ragged size. Under
`CRANELISP_RC_DEC_CHECK` the armed lane would hard-fail at the first string
`consume_shallow`/`dealloc` in any real program: the A-row proofs would pass
(their fixtures are 8-aligned marker blocks), while the armed acceptance legs
Track B and 0859 depend on would abort on correct programs. The design's own
`scrub` already handles the ragged case (`scrub_poisons_nonmultiple_of_8_tail`),
so the layout fact is known in the crate — §7.5's alignment clause reads as an
oversight rather than an intent.

## What was implemented instead (and why it is not weaker)

`diagnostics::header_size_plausible(alloc_size)` accepts iff the value converts
to `usize`, is `>= HeapHeader::SIZE`, and forms a valid
`Layout::from_size_align(size, 8)`. Both faces §7.5 names as the clause's
motivation are still caught:

- **poisoned/quarantined base** (A3/A4): `POISON_WORD` read as `i64` is
  negative, so the `usize` conversion fails — rejected. The Layout clause also
  rejects any implausibly-huge magnitude, which is what delivers §7.5's stated
  goal ("a located seam message instead of a `Layout` panic") — the alignment
  clause alone would not have, since a poisoned header read as `usize` is
  8-mis-aligned *and* Layout-invalid.
- **interior/non-base address** (A2): word@0 is a tag / length / field value,
  far below `HeapHeader::SIZE` — rejected by the size clause. The A2 triplet's
  positive asserts `alloc_size=3`.

Coverage of the deviation: `precheck_accepts_a_ragged_heap_string_size` (the
false-positive fence), `precheck_rejects_a_poisoned_header_word`,
`precheck_rejects_sizes_below_the_header`, plus the four A-row triplets and the
`RC_DEC_CHECK`-armed clean control
(`clean_heap_workload_balances_at_every_seam`, which allocates a ragged string
under the armed gate on purpose).

## Ask of `/design`

Amend §7.5's predicate (a) and the §5 A2/A4 amendment to state the
Layout-validity form, or rule that the alignment clause is wanted and name the
`HeapString` disposition (a layout change is a version bump, not a guard —
`CLAUDE.md` §"Heap layout"). The grading language ("plausibility, not proof of
basehood") is unaffected either way and `/qa`'s 0857 regrade can proceed against
the implemented predicate.
