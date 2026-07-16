---
number: 24
title: Resolve once
---

# Principle 24 — Resolve once

> Authored S110 Phase 3 (motivating context: FIXME 0583, the backend name
> resolver — the "two resolvers, one name" mirror class that recurred 3× in
> S109; user directive S109 P5). **Strengthened S110 Phase 7** (user
> direction): the no-scan invariant is stated compiler-wide, resolution
> itself is characterized as a keyed-lookup chain, and the enumeration +
> `/search` carve-outs are made explicit. **RATIFIED at S110 Phase-7 close
> (user-approved 2026-07-16)** with the strengthened wording, per the
> close-only register rule (the P21/P23 precedent).

**Statement.** A semantic identity — a name, a type, a member, a dispatch
target — is derived at exactly ONE pipeline stage and crosses every stage
boundary as a resolved, fully-qualified VALUE (`FQSymbol`, `FQTypeName`, a
storage key). Downstream stages perform keyed reads against that value and
hard-fail on a miss (Principle 18); they never re-derive the identity from the
written name, and they never carry a second copy of the derivation rules.

**And the derivation itself is a keyed-lookup chain, not a search.** There is
no valid search for a compile-necessary identity — anywhere in the pipeline,
the producing stage included. The one construct that looks like an exception —
the import/re-export chain — is not one: it is a bounded, deterministic
sequence of keyed lookups following explicit pointers (`table.get(name)`; if
the entry is an `Import`/`Reexport`, follow its explicit `(module, name)`
target and `get` again, until a real `Def`). The lexical scope stack is the
same shape locally (innermost-frame-first `get` with language-defined
shadowing precedence), and the prelude fallback is ONE more keyed lookup at a
designated table (spec §8.6.4 — prelude ≡ explicit import). At every step the
next key is determined either by language-defined precedence or by an explicit
pointer carried on the entry just fetched — never by enumerating what happens
to exist. There is no privileged search hiding inside the resolver.

**What the principle forbids — the ambient scan.** An ambient (unindexed) scan
— `symbol_tables.iter()`, try-every-module, first-match-by-iteration-order —
is forbidden as a source of compile-necessary identity at EVERY stage, not
just the backend. The acid test: *does the answer depend on which entries
happen to be present elsewhere, or on the order a collection iterates?* If
yes, it is an ambient scan, and its result may not become an identity the
compiler acts on. A chain's step order is a function of the program text
(scope precedence, the fetched entry's pointer); a scan's order is incidental
(hash order, insertion order, directory order) — dependence of the answer on
incidental order IS the divergence surface. The honest answer to "name one
valid search for identity" is: none.

**Two carve-outs, so the invariant does not over-reach:**

1. **Enumeration is not a search.** Reading ALL rows of an indexed set — a
   module's public entries (glob import, `/exports`), an `Overloaded` def's
   variants, a sum type's constructor set (exhaustiveness), the importable
   index — is a complete-by-construction read whose answer is a function of
   the complete set, hence order-independent. Its failure mode is
   *incompleteness* (a source missing from the union — the S108
   enumeration-miss class; governing rule: one reader per kind, every source
   contributes rows or a legal skip — `resolve-home-enumeration.md` §3), never
   divergence. Dispatch selection is this shape: the candidate set is keyed
   (all variants under one FQ name; all impls at the trait's home module,
   Decision 0045), and the pick is a type-match *computation* over that
   complete set — not a scan for the data. The discipline that keeps an
   enumeration on the right side of the line: the consumer uses the COMPLETE
   set, and a tie is an ambiguity error, never broken by iteration order. An
   enumeration that returns the first match of a many-candidate set has become
   a scan.

2. **The one sanctioned genuine scan in the compiler is `/search`** — the REPL
   discovery command. It is allowed to scan precisely because it is NOT
   resolution: it produces candidates for a human to read, never an identity
   the compiler acts on (the introspection-is-REPL-only ruling — D1, S80,
   `design/arch/d1-introspection-repl-only.md` — draws the same boundary:
   compile-necessary data lives on the symbol table, never on a
   discovery/introspection surface). Any future mechanism claiming the same
   license must satisfy the
   same criterion — human-facing candidates only, REPL-only — and be named
   here.

**Rationale.** A re-derivation downstream is a second resolver, and two
resolvers for one name WILL diverge — not hypothetically but as a recurring
defect class: the backend's `resolve_driven` global scan re-resolving names
typecheck had already resolved produced the S109 one-hop-vs-multi-hop `unknown
constructor` cascade, the silent nullary-ctor-as-closure wrong-value split,
and the DC-11 scrutinee-directed wrong-tag RUN-TO-RUN NONDETERMINISM (3
instances, one root — FIXME 0583). The same shape recurs within a stage:
typecheck's four written-type-var resolver mirrors each minting on their own
(0590), the per-position value-mint whitelist re-deciding "is this a value
position" at each site (0585), and the twice-derived ADT-entry construction
(bootstrap ≡ adt.rs, audit R-2) where one keying change had to be hand-applied
to both copies. Principle 7 states single-source; this principle binds the
STAGE question P7 leaves open — the source is the stage where the identity is
first derived, and everything after it is a consumer. Re-derivation is not
merely duplication: the downstream copy runs in a different context (different
scope, different precedence inputs, different iteration order), so its
divergence is silent and often nondeterministic. The strengthening is not
backend-specific because the failure is not: an ambient scan's dependence on
population and iteration order is intrinsic to the scan wherever it runs —
0583's wrong-tag nondeterminism came from an iteration-order fallback, and the
same mechanism produces the same nondeterminism at any stage. The backend
grep-zero (BC §3 invariant 10) is therefore the first instance of a
compiler-wide invariant, not a backend rule.

**Consequence.** Resolution results are recorded where resolution happens (the
producing stage's chokepoint) and transported as data — on the AST/mono node
or a span-keyed sidecar, persisted with the entry when the consumer can run
from cache. The consumer's read is a direct keyed fetch: no precedence walk,
no import-chain re-follow, no fallback scan; a missing key is a hard, located
error, never a re-derivation (a keyed-read-else-re-resolve hybrid is the
Principle-8 half-measure and is a review REJECT). Where several sites inside
one stage need the same derivation, it is one function with thin callers, and
the carrier parameter is REQUIRED so a new site cannot forget it
(Principle 18's unforgettable-parameter form). Instances unified under this
principle: 0583 (backend keyed-lookup consumer — the typecheck→backend seam;
`design/arch/backend-keyed-consumer.md`), the S109 §10/DC-11 pattern-position
cure (retrospectively its first application), 0590 (one written-type-var
resolver), 0585 (one value-position enumeration for mint and die), R-2 (one
ADT-entry derivation, `cranelisp_types::build_adt_entries`). The backend's
end-state under this principle is a PURE keyed-lookup consumer: zero name
resolution, zero bare-type-name resolution (BC §3 invariant 10).

**Enforcement consequence.** Under the compiler-wide statement, any ambient
identity-scan anywhere in the pipeline is a defect this principle names: an
unindexed iteration whose result flows into a compile-necessary identity is
grep-visible and a review REJECT, while complete-set enumeration sites (trace
descriptor baking, utilization reports, swap-all-table walks) are legitimate
under carve-out 1. A compiler-wide sweep classifying every unindexed iteration
as enumeration-or-scan is a well-defined audit task (scheduled S111). An
implementation found scanning for identity is never counter-evidence against
this wording — it is an instance of the defect class the principle exists to
eliminate.
