---
id: ACT-0961
title: Revisit with the user whether an import may introduce a conflicting name
status: deferred
priority: advisory
from: spec
to: spec
sprint: 122
filed_at: 2026-09-20
refers_to:
  - spec/08-modules.md
  - repl/spec/04-self-documentation.md
---

## Request

On 2026-09-20, while ruling on REPL introspection display for a spelling with
several candidates, the user observed that the language rule itself may be
mistaken — "you shouldn't be able to import conflicting names" — and explicitly
deferred any correction. This action carries that deferral; it is not authority
to change the language now.

**Current authority (unchanged).** `spec/08-modules.md` §8.6.4 permits a
module-local declaration, an `import`/`export`, an implicit-prelude binding and
a derived member to expose the same unqualified spelling when their canonical
identities are distinct: registration is not an error, does not shadow, and does
not depend on order or mode. §8.6.2 deduplicates candidates that reach the same
terminal identity and keeps distinct terminals as peers. §8.6.5 rejects only the
*use*: an unqualified use surviving with several candidates is ambiguous and must
be canonically qualified or annotated. `repl/spec/04-self-documentation.md`
§4.1.11 lists every candidate at introspection and raises no ambiguity of its own.

**Intended direction to put to the user.** The candidate case is narrow: the
same local spelling arriving from *distinct canonical declarations* that also
share a type, where no use site can ever select one without qualification, so
registration could reasonably be rejected at the import rather than deferred to
every use. Do not widen this to disallowing all same-spelled imports —
differently-typed peers resolve normally under §8.6.5 and §8.6.4 deliberately
admits them.

Source verified on filing: opened `spec/08-modules.md` §8.6.1–§8.6.5 and
`repl/spec/04-self-documentation.md` §4.1.11 and confirmed each statement above
against that prose.

## Completion evidence

Put the question to the user as prose (problem / resolution / tradeoffs), stating
what §8.6.4 permits today, what the narrow restriction would reject, and its cost
— error timing, prelude and glob interaction, re-export chains, and what breaks
for a module that currently imports differently-typed peers. Record the ruling and
update `spec/08-modules.md` only if the user rules for a change, invalidating the
affected coverage annotations in the same edit and reporting the changed
obligations to `qa`. A decision to keep §8.6.4 as it stands resolves this action
with its rationale recorded.
