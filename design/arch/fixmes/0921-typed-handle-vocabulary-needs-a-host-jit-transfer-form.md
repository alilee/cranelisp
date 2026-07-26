---
number: 0921
target: /design
filed_by: /design
filed_at: 2026-07-26
sprint_filed: 119
refers_to: design/arch/ownership-stratum-options.md §2.1/§2.3 (tranche A vocabulary);
  design/int/macro-turn-ownership.md §3 Rules 3/4/6 and §12;
  crates/cranelisp-intrinsics/src/drop.rs:156 (consume_slist), :214 (consume_sexp);
  src/expander.rs:512-549 (invoke_clause)
status: open
---

# Tranche A's `Owned`/`Borrowed` vocabulary: three requirements from the tranche B-int consumer

**Target: `/design`(runtime pair — `cranelisp-primitives` + `cranelisp-intrinsics`).**
Filed by `/design`(int) alongside the tranche B-int ownership ruling
(`design/int/macro-turn-ownership.md`), per `sprints/SPRINT.md` §Spine 2: tranche
B is a **third** typed surface consuming the intrinsics-public vocabulary, and
`/arch` verified no `consume_*` call exists in `src/` today — B *introduces* the
discipline there. This FIXME states what int needs so the vocabulary is designed
with its third consumer visible, rather than retrofitted.

## Issue

The tranche-A design is authored against the pair's own consumers (36 `consume_*`
call sites, 83 extern shims). The int-side macro-turn boundary is a different
shape: it is a **host↔JIT** boundary that is not an `extern "C" fn` declaration —
int holds a raw entry pointer and `transmute`s it to
`extern "C" fn(i64) -> i64` (`MacroClauseAbi::SexpListToSexpI64V1`). Three
consequences:

1. **Transfer across a non-`extern` boundary.** §2.1 says "the typed layer begins
   at the extern shim" and names discharge as "pass by value into a consuming fn,
   a store into a structure, return across the ABI shim". Int's transfer happens
   at a `transmute`d call site with no shim to hang the annotation on. Int needs a
   documented, explicit conversion pair — an `Owned → i64` consuming form and an
   `i64 → Owned` adopting form — that the vocabulary blesses as the ABI-crossing
   discharge/acquisition, rather than each consumer inventing one. Int's Rule 3
   depends on the **outbound** form being a genuine discharge (it is what makes
   the JIT trap path correct by construction: after the conversion int holds
   nothing, so an abandoned longjmp'd frame forfeits nothing int must clean up).
   The inbound form is the one honest-limit widening §2.2 already names — it is
   the shim lying — and should be marked as such at the site.

2. **Bare nullary tags must be representable as handles.** Every word below
   `NULLARY_TAG_THRESHOLD` is data, not a pointer; `build_runtime_slist(&[])`
   legitimately yields `TAG_SNIL` (0), and a nullary macro's whole args list is
   that word. `Owned` must **tolerate** such a word: constructing it is legal and
   discharging it is a no-op. Every intrinsics consume entry already guards this
   (`ptr < NULLARY_THRESHOLD → return`), so tolerance costs nothing — but if the
   newtype's constructor refuses or debug-asserts a non-pointer, int is forced
   into a second code path at exactly the shape most likely to be exercised.

3. **`consume_sexp` / `consume_slist` reachable with typed signatures from a
   third crate.** Both are `pub` in `cranelisp-intrinsics::drop` today. Int's
   Rule 4 discharges the expansion result through `consume_sexp` and nothing else
   — there is exactly one releaser and it must stay in intrinsics. If tranche A
   narrows either to `pub(crate)` or routes it behind a pair-internal wrapper,
   int loses its releaser and would be pushed toward a private traversal in
   `src/marshal.rs`, which is the mirror class this whole spine exists to remove.

## Proposed resolution

Confirm (or design) the three in tranche A: the ABI-crossing conversion pair as a
named, documented part of the vocabulary; nullary-tag tolerance stated in the
newtype's rustdoc; and `consume_sexp`/`consume_slist` remaining `pub` with typed
signatures. If any is out of scope for tranche A, say so and int will state the
gap in `macro-turn-ownership.md` §12 rather than work around it.

## Context

Sequencing is already correct: tranche B is strictly after tranche A ("the
vocabulary must exist and be consumer-proven first", §2.3). This is a
requirements handoff, not a blocker on A's design. `/arch` holds the boundary
question separately (FIXME 0922 — the macro-clause ABI ownership declaration).

## A separate, confirmed intrinsics gap surfaced while ruling the protocol

**`consume_sexp` does not know about `TAG_SEXP_ANNOTATED`, and this is a leak
that exists today, independent of 0889.**

Verified by grep at HEAD: `cranelisp_types::TAG_SEXP_ANNOTATED = 7`
(`crates/cranelisp-types/src/marshal.rs:77`, pinned by
`marshal/tests.rs:42`), and **`cranelisp-intrinsics` never names it** — zero
occurrences in the crate. `drop.rs::consume_sexp` (`:243-255`) dispatches
`TAG_SEXP_STR|TAG_SEXP_SYM` → `consume_shallow(field0)` and
`TAG_SEXP_LIST|TAG_SEXP_BRACKET` → `consume_slist(field0)`, and falls everything
else through to `_ => { /* SexpInt/Float/Bool — field0 is a scalar, no RC */ }`.
Its rustdoc enumerates tags 0–6 only. An annotated cell is the **only two-field**
runtime Sexp (`src/marshal.rs::alloc_sexp_pair`, `field0` = annotation, `field1`
= subject, both heap `Sexp` pointers), so consuming one today discharges neither
field and deallocs the parent — leaking both subtrees.

This is the S116 `annotated-sexp-node.md` cascade's intrinsics-side residue: the
8th `Sexp` constructor was appended in types, frontend, and both bootstrap seeds,
and the consume path was not extended with it. It is reachable now wherever a
`consume_slist` walk reaches an annotated head; tranche B-int's Rule 4 makes it
**definitely** reachable, because int will discharge every expansion result
through `consume_sexp` and `:~T x` folds to an annotated node at read time.

`/design`(int) has made confirming-and-fixing this a `/dev` gate
(`macro-turn-ownership.md` §8 D2). The fix belongs in `drop.rs` — a
`TAG_SEXP_ANNOTATED` arm discharging both fields, plus a unit row — and **never**
as a compensating walk in `src/marshal.rs`.
