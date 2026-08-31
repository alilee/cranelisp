# design/arch/principles/

Architectural Principles register. One file per Principle: `NN-{slug}.md` with frontmatter `number: NN, title: ...`. The index `design/arch/principles.md` is the **single carrier of the principle set**: a Principle is in force when it is indexed there, and nothing else enumerates the set.

## How a Principle reaches a role

`arch`, `design`, `dev` and `review` read `design/arch/principles.md` as a first-read of every dispatch. `sprints/METHOD.md` §1.1 states the obligation; the consumer adapter of each of these roles at `.claude/agents/<role>.md` names the index in its entry text. The index carries one line per Principle, so a role that has read it can tell which body file governs the choice in front of it and cite by name.

This replaced the retired `@` import blocks — one in the `arch` command file and one in each triad command file, all four required to list the identical set (S120). Copying membership four times drifted twice, S65 and S76, leaving Principles on disk invisible to the roles applying them for whole sprints. One carrier removes the class; do not reintroduce per-adapter enumerations of the set.

Assurance grade: measured for repository reachability. The standing
`scripts/verify-role-wiring.py` gate reconciles Principle files against the
index (W5) and checks that every obliged host adapter names the first-read (W6).
`tests/role_wiring.rs` proves both conditions detect planted faults and clears
an unmodified copy. Whether a dispatched role actually applied a governing
Principle remains review evidence: its falsifier is a `review` finding naming a
Principle the change should have cited but did not.

## Authoring a Principle

Principles are added at sprint close (Phase 7 review), never mid-sprint. The filer does all of it in one change-set:

1. Create `NN-{slug}.md`, numbered above the highest used, stating the rule and its acid test and citing the motivating sprint.
2. Add the index line to `design/arch/principles.md`: number, link, title, one-sentence statement, motivating context.

Nothing else needs editing — reachability is the index.

## Editing a Principle

Revise the body file and, when the statement changes, its index line, at sprint close; cite the motivating sprint in the body and in the sprint outcome report. Then sweep the canonical set for references the change touches (`design/arch/CLAUDE.md` §Where a commitment manifests).

## Retiring a Principle

Delete the file (git history keeps it) and remove its index line in the same change-set. The pair moves together: a lingering index line points at nothing; a lingering file is out of force yet found by search.
