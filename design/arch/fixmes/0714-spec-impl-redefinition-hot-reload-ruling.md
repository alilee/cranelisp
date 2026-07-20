---
number: 0714
target: /spec
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 114
refers_to: spec §7 (traits/impls) + §18 (redefinition semantics); tests/impl_redefinition_dispatch.rs::reimpl_either_dispatches_new_or_notices_not_replaced (the polarity-safe pin, RED)
status: open
---

# Scribe the impl-redefinition ruling: hot-reload with defn's same-type constraint

**USER RULING (2026-07-20, S114 Phase 7 close): impls SHOULD be hot-reloaded,
carrying the same same-type constraint as `defn` redefinition** (§18 semantics:
a re-`impl` of an existing (trait, type) pair replaces the previous impl and
subsequent dispatch uses the new body; the method's signature must satisfy the
same-type constraint that governs `defn` redefinition, else the redefinition
rejects the same way).

Scribe into spec §7/§18 (whichever owns redefinition semantics; cross-link).
Discovered by /repl's S114 Phase-6a probe: today the re-impl prints the normal
confirmation line but the FIRST impl still dispatches — a silent-accept. The
polarity-safe pin above goes GREEN when /dev implements hot-reload (its
"dispatch reflects the new impl" branch is now the required behavior; the
"not-replaced notice" branch is dead under this ruling — /testing may sharpen
the pin to hot-reload-only when the fix lands). Fix owner: /dev (src impl
registration/dispatch seam per the pin's locus), S115 scope input.
