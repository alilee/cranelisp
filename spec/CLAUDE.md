# spec/

The Cranelisp language specification — the authoritative record of what the
language does. Owned by the `/spec` skill.

## Role of `/spec`

`/spec` is a **scribe**, not an arbiter. It records semantics that are already
settled and keeps the spec internally consistent. Every open normative question
— what the language *should* do — is brought to the **user**, who arbitrates.
`/spec` frames such questions as prose (problem / options / tradeoffs) and does
not rule on them itself. This mirrors `.claude/commands/spec.md`.

## Authority

The spec is the source of truth for the reimplementation. When implementation
and spec disagree:

- **Spec is correct** → the implementation is the defect; the owning compiler
  skill fixes it.
- **Spec is wrong or silent** → this is a normative question. `/spec` does not
  quietly rewrite the spec to match whatever the compiler happens to do; it
  brings the divergence to the user, records the ruling, then updates the spec.

The sketch oracle is **retired** (deleted at Sprint 87; language semantics are
frozen — see root `CLAUDE.md` §"Sketch Oracle"). Ambiguity is resolved with the
user, not by running a prototype.

## Scope boundary

The spec defines the **language** and the requirements it places on a
conforming compiler. It does **not** prescribe the standard library — there may
be multiple stdlib candidates. Section 11 and Appendix A are non-normative
reference documentation for the reference implementation's stdlib.

## Conventions

- Sections 1–10, Section 12, and **Appendix C** (non-functional requirements)
  are **normative**. Section 11 and Appendix A are **non-normative** reference.
- Keywords MUST, MUST NOT, SHOULD, SHOULD NOT, MAY follow RFC 2119 semantics.
- EBNF grammar, typing rules, and evaluation judgments in each section are
  authoritative. Examples define expected behaviour.
- **Traceability annotations** (`[Tested …]`, `[Tested+Neg …]`, `[S{M}]`, the
  test-side `// spec:` comment) are governed by root `CLAUDE.md`
  §"Requirements/Test Traceability" — that is canonical; follow it, don't
  restate it here. Tests are authored by `/testing` to `/qa`'s plan; `/qa`
  audits the two-sided spec↔test match.

## Files

Naming convention: `NN-topic.md` for the twelve numbered sections (01 lexical →
12 runtime), `appendix-{a,b,c}-*.md` for the three appendices (a builtins,
b examples, c NFRs). Two meta files sit alongside: `index.md` (front matter,
version, design philosophy) and `ring0-readiness.md` (a dated Sprint-0
acceptance record; historical, kept for provenance).

## Cross-skill changes

Another skill that needs a spec change files a numbered FIXME —
`design/arch/fixmes/NNNN-short-name.md` (protocol: `sprints/METHOD.md` §3.3) —
and `/spec` evaluates it, actions it here, and deletes the FIXME file. Inline
`FIXME(/spec)` comments are the **old** protocol (superseded Sprint 63); do not
author new ones.
