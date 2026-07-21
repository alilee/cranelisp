---
number: 0818
target: /qa
filed_by: /sprint
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/arch/fixmes/0604-index-feed-phantom-prelude-write-race.md
  (§"The defect" — the exact error signature) + the /stdlib S115 Phase-6a
  assessment (disclosed probe contamination, dropped candidate FIXME 0818's
  original subject) + sprints/METHOD.md §2.2 "Probe hygiene: the repo root is
  not a clean room"
status: open
---

# 0604's signature was reproduced from probe contamination alone — a lead on the three-sprint heisenbug

## Issue

**This is evidence, not an attribution.** `/stdlib`, during its S115 Phase-6a
sweep, ran probes in a **single shared scratch directory**, which accumulates a
persisted REPL `user.cl` across probes. In that contaminated directory it
observed:

```
ambiguous bare name 'bit-and' … num.bits/bit-and … primitives/bit-and
```

on `(import [primitives [*]])`. It was one step from filing that as a new
defect. Re-run in a **pristine per-probe directory**, `(bit-and 12 10) ⇒ 8` and
the error does not occur. `/stdlib` dropped the finding, disclosed the
contamination, and re-ran every other finding pristine (all survived).

**That signature is FIXME 0604's signature** — the same name, the same two
sources, the same ambiguity shape that 0604 has carried for three sprints as a
phantom public `bit-and → primitives/bit-and` entry in prelude's live table.

## Why this is worth /qa's time

0604's defining property is that it will not reproduce on demand: **16/16 in
one environment, 0/140 in another, 25/25 at S114 W5, then 0/85 and 0/496 under
load at S115.** The record already concludes that quiet sweeps are spent
evidence. What has never been explained is why the *firing* environments fired.

Session-state contamination is a candidate that fits the fingerprint in a way
scheduling never quite did:

- it is **environment-resident, not timing-resident** — which explains
  determinism within an environment (25/25) and total absence in another
  (0/140), where a race would be expected to smear;
- it is **invisible in the repo** — `user.cl` is git-ignored, so no diff, no
  bisect, and nothing an investigator would think to clear;
- it explains why the S115 structural gate landed, swept clean, and could not
  be credited with a fix: **it may never have been the same defect.**

## Proposed resolution

`/qa` holds 0604's disposition (S115 W3 ruling; retirement is currently gated
on the census rows). Suggested next acts, cheapest first:

1. **Try to reproduce 0604's recipe deliberately in a contaminated
   directory** — seed a REPL session that persists definitions touching
   `bit-and`/`num.bits`, then run the recipe. If it fires, the heisenbug has a
   mechanism and a deterministic trigger for the first time.
2. **Check the firing environments' shape against this hypothesis** — the S109
   `/sprint` environment (16/16) and the S114 W5 `/dev` environment (25/25)
   are both recorded; if either was a long-lived working directory with a
   persisted session file, that is corroboration.
3. **If it holds**: 0604's attribution changes from "a phantom write by some
   producer" to "session persistence re-entering the live table", the
   structural gate remains correct and useful on its own merits, and the
   register row R7's status can be re-stated honestly.
4. **If it does not hold**: record the falsification — the hypothesis is cheap
   to test and its refutation is worth as much as its confirmation, since it
   removes the most plausible remaining non-scheduling explanation.

Note for whoever runs this: METHOD §2.2's probe-hygiene rule landed **this
sprint**, one day before `/stdlib`'s sweep manufactured this signature — and
the rule's own worked example was a *different* false diagnosis from the same
repo-root `user.cl`. That file has now produced at least three spurious
findings in one sprint. Whatever 0604 turns out to be, the contamination
surface is real and measured.
