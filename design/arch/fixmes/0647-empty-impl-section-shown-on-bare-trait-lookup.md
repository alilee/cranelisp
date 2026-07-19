---
number: 0647
target: /dev
filed_by: /repl
filed_at: 2026-07-18
sprint_filed: 112
refers_to: src/ (int) trait-lookup display — the `; impl:` drawer under §4.1.4; repl/spec.md §4.1.3/§4.1.4
status: open
---

# Bare trait lookup prints an empty `; impl:` section when the trait has no implementations

## Context (severity: low, display consistency)

Observed on the b2 binary (S112), default prelude session:

    user> (deftrait Sizeable (size [x] Int))
    :user/Sizeable ; deftrait
    ; defn:
    ;  size

    user> Sizeable
    :user/Sizeable ; deftrait
    ; defn:
    ;  size
    ; impl:            <-- empty drawer, no members

The bare-symbol lookup prints a `; impl:` header with **nothing under it** when
no type implements the trait yet. Two inconsistencies:

1. The `deftrait` **echo** (definition-time display) omits the `; impl:` section
   entirely; the bare **lookup** shows it empty. §1.3 says a definition is
   "immediately followed by its lookup display" — the two should match.
2. The `deftype` path already **omits** empty related-symbol sections: a fresh
   `(deftype Box ...)` with no impls shows only `; match:`, no empty `; impl:`.
   The trait path diverges from that established convention.

## Attribution

Pure display behaviour, int-side (the trait-lookup formatter). Not a semantic
defect — no wrong data, just an empty drawer. `repl/spec.md` §4.1.4 examples only
ever show a populated `; impl:`; the spec is currently silent on the empty case,
so this is a consistency wart rather than a hard spec violation. (If /arch/spec
prefer "always show the drawer" over "omit when empty", `/repl` will pin that in
§4.1.4 instead — but the deftype precedent argues omit-when-empty.)

## The ask (/dev)

Omit the `; impl:` section on bare trait lookup when there are no implementations,
matching the `deftype` `; match:`/`; impl:` omit-when-empty behaviour, so the
echo and the lookup agree. `/repl` will add the omit-when-empty rule to
§4.1.3/§4.1.4 as the normative statement once the direction is confirmed.
