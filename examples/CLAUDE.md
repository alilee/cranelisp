# examples/ — the learning sequence

Owned by `training`. The sequence is the product, not the individual programs:
each one introduces what a reader cannot yet do, rests on what precedes it, and
earns its place. `plan-examples.md` carries the intended arc; the numbered files
on disk are the sequence of record.

## Every example runs, always

**A broken example is worse than an absent one** — it teaches a reader that the
language is broken, and a reader cannot tell which of the two of you is wrong.

1. **Only ship what passes.** Verify before committing:
   `./target/debug/cranelisp --run examples/NN-name.cl`.
2. **Only teach what exists.** Write examples for delivered behaviour, never for
   planned behaviour. If a feature is not available in batch mode yet, its
   example does not exist yet.
3. **Verify the whole sequence every sprint**, at open and at close, not only
   the files that changed. Zero broken examples is a hard gate; a compiler
   change that breaks one is a defect routed to `qa`, not a reason to quietly
   drop the example.
4. **Test mode.** Every example defines `main` returning an `Int` — a sum of
   sub-test results, 1 per pass and 0 per fail — so a non-zero result means the
   example verified itself. A zero return is a failure even when the run exits
   cleanly.
5. **Free-standing.** Examples MUST NOT depend on `stdlib/`; they define helpers
   inline from primitives and special forms, so the sequence validates the
   language rather than the library. This is the root `CLAUDE.md` §Design
   Principles stdlib-separation rule, and `examples/lib/` is where shared inline
   helpers live.

## Gate before handing back

`cargo build` clean, then every `examples/*.cl` runs and returns non-zero. Do not
report completion with a broken example. If a compiler change broke one, file
the defect and either adjust the example away from the broken feature or
withdraw it until the feature works — recording which, and why, in the report.

## The standing question

The `training` contract asks it against the whole sequence every increment, not
against the delta: coverage (what is unteachable from the sequence today?),
order, nuance (does it teach boundaries, traps and negative space?), and
readability as reading material. Answer it whether or not the brief asked.
