---
number: 0409
target: /repl
filed_by: /sprint
filed_at: 2026-06-20
sprint_filed: 86
refers_to: repl/demos/CLAUDE.md §"The active set", repl/showcase (list_demos), repl/demos/demo-player.py
status: open
---

# Surface the showcase demos' guided order (number them)

## Issue

Surfaced during S86 UAT. The eight active showcase demos have a deliberate
pedagogical arc (`tour → values-and-types → adts-and-matching → functions →
traits → modules → io-and-effects → sudoku`), documented in
`repl/demos/CLAUDE.md` §"The active set". But that order is **invisible to a
viewer**:

- `./repl/showcase --list` calls `sorted(DEMOS_DIR.glob("*.demo"))` — pure
  alphabetical, so the listed order is `adts-and-matching, functions,
  io-and-effects, modules, sudoku, tour, traits, values-and-types` —
  pedagogically scrambled (Sudoku, the centerpiece, lands 5th; `tour`, the
  intended start, lands 6th).
- A user who watches `tour` first (as intended) then has no cue what comes next.

The content is good; only the **sequencing affordance** is missing.

## Proposed resolution

Number the active-set demo files so the order is self-evident — matching the
convention already used in `examples/` (`08-floats.cl`, `21-hello-io.cl`, …),
which numbers precisely so the learning sequence is legible:

```
01-tour.demo
02-values-and-types.demo
03-adts-and-matching.demo
04-functions.demo
05-traits.demo
06-modules.demo
07-io-and-effects.demo
08-sudoku.demo
```

Benefits:
- Numbered filenames make the existing alphabetical `--list` sort **coincide**
  with the pedagogical order — the scramble disappears with no special sort
  logic.
- The arc is visible at the filesystem level and in `--list`.

Implementation notes:
- **Preserve name resolution**: `./repl/showcase sudoku` (and `tour`, etc.)
  must keep working — resolve a bare name against the numbered stem suffix
  (`*sudoku.demo`), not require the number. Don't break the muscle-memory
  invocation.
- Update `repl/demos/CLAUDE.md` §"The active set" table to show the numbered
  filenames, and confirm "watch in order" guidance points at the numbers.
- Archive demos (`archive/`) stay as-is — they are regression guards, not part
  of the guided narrative, so they don't need numbering.
- Consider having `--list` print the active set under a "Guided order" heading
  so the intent is explicit even to someone who doesn't notice the numbers.

## Operational implication / Context

- `/repl` owns `repl/` and the showcase; this is a `/repl` change. Filed by
  `/sprint` from UAT feedback, not actioned in-place.
- No language/compiler dependency — purely a discoverability/affordance fix to
  the demo set and the `showcase` script.
- Small, self-contained; good candidate for the next `/repl` pass.
