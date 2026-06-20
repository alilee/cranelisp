---
number: 0415
target: /repl
filed_by: /sprint
filed_at: 2026-06-20
sprint_filed: 86
refers_to: repl/spec.md §3.3 (Large category display layout algorithm), §3.4 /imports, §3.5 /exports, §3.3 related-symbol lists (repl/spec.md:198)
status: open
---

# Symbol-layout (line-breaking) algorithm is a SHOULD with no test coverage

## Issue

Surfaced during S86 UAT. `repl/spec.md §3.3` defines the multi-column
line-breaking algorithm for displaying symbol names when a category has **7 or
more** names:

1. **Operators first, then a mandatory break** — non-alphabetic symbols
   (`+ - * != …`) display first, 6 per line; operators never share a line with
   alphabetic names.
2. **Letter groups pack onto rows but break early to stay together** — group by
   first letter (case-insensitive, sorted); before adding a group to the current
   row, if `current_count + group_size > 6`, flush the row first; a group never
   splits across a row boundary unless it alone has 7+ names.
3. **Hard wrap at 6** within an oversized letter group.

Categories with <7 names appear on a single line after the label.

This algorithm is **shared by `/list`, `/imports`, and `/exports`** (§3.4 and
§3.5 both say "same layout algorithm as §3.3"), and by related-symbol lists
(repl/spec.md:198). It is therefore a high-traffic, user-facing formatting
contract.

Two problems:
- **It is a SHOULD, not a MUST** ("the display SHOULD use the following layout
  algorithm"). An implementation could legitimately diverge, which makes it
  untestable-as-written (you can't assert exact output against a SHOULD).
- **It has zero test coverage** — the spec carries only an illustrative example
  block with NO `[Tested …]` annotation on any of the three steps. None of the
  three commands' wrap behaviour is pinned by a test. So the precise column
  layout the REPL actually produces is unverified against the spec.

## Proposed resolution

1. **/repl decides normativity.** Promote the layout to a **MUST** (with the
   exact algorithm as the normative contract) so it is testable, OR keep it a
   SHOULD and explicitly state that the example shows the *reference* layout that
   tests assert as expected-but-not-mandated. Recommend MUST — exact, scannable
   symbol layout is a self-documenting-REPL feature and divergence across the
   three commands would be a real inconsistency.
2. **Hand to /qa for coverage** (once normativity is fixed): author tests that
   pin each rule against real REPL output —
   - operators-first + mandatory break (a category mixing operators and names),
   - letter-group early-break (groups that would exceed 6 on a row),
   - hard-wrap-at-6 within an oversized single-letter group,
   - the <7-names single-line case,
   - and that the **same** layout is applied by `/list`, `/imports`, AND
     `/exports` (one shared formatter, not three divergent ones).
3. **/repl annotates** §3.3/§3.4/§3.5 with the resulting `[Tested …]` once
   covered.

If S86 UAT (or this work) reveals the live REPL output diverges from the
algorithm, that is a defect — /qa files a failing-not-ignored repro and the
owning skill (/int, `src/pretty.rs` / the symbol-list formatter) resolves.

## Operational implication / Context

- /repl owns `repl/spec.md §3.3`; the normativity call is theirs and gates the
  test shape. /qa writes the tests; /int owns the formatter if a divergence
  defect surfaces.
- Related to the broader spec→test reconciliation (FIXME 0412/0413) but distinct:
  this is a genuine **coverage gap on an untested requirement**, not a rotted
  citation pointing at a deleted test.
