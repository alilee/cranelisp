---
number: 0702
target: /spec (re-targeted by /qa, S114 pre-W7 disposition — the three-way
  disagreement gates cell polarity; /qa's matrix half is discharged, see the
  disposition section)
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
scheduled: S115 (chain: /spec ruling → /design(frontend) premise correction →
  /testing M3 cells + /dev(frontend) predicate widening)
refers_to: spec/05-definitions.md §5 binder-positions table; crates/cranelisp-frontend/src/ast_builder.rs::reject_qualified_binder_head; design/frontend/binder-head-reject.md §2 (the `.` de-scope note); tests/plan/s114-test-plan.md §5.1 M3 (the standing matrix)
status: open
---

# Dotted-spelling binder axis unenforced — spec §5 [S113] MUST vs `/`-only predicate

## Severity
Important

## Issue

Spec §5's binder-positions prose (scribed [S113]) is categorical: *"A binder
therefore never carries a module qualifier (`/`, §1.4.3) **or a dotted path
(`.`, §1.4.4)** … A qualified **or dotted** spelling in **any** binder position
is a compile-time error."* The implemented reject (`reject_qualified_binder_head`,
`ast_builder.rs:70` via `split_qualified_name`) keys on `/` ONLY, per
`design/frontend/binder-head-reject.md` §2's de-scope note — whose premise
("a dotted name … never appears in a raw declaration-head slot") is **falsified
by probe**. Observed on HEAD `8b2c3e20` (all `PreludeVariant`-free REPL probes):

| Probe | Face |
|---|---|
| `(defn a.b [x] x)` | **silently binds** `user/a.b` (`; defn` echo) |
| `(deftype A.B [:Int v])` | **silently accepts**; echo shows type `user/A.B` but ctor **`user/B`** — the dotted head corrupts the ctor identity downstream (something splits at `.`) |
| `(deftype P [:Int a.b])` | accepts with a suppressed-accessor warning (dotted FIELD name — §5 table says field binder rejects qualified) |
| `(let [a.b 5] a.b)` / `(defn g [a.b] 1)` / `(match 1 [a.b a.b])` | all **silently bind** a dotted local |
| `(deftype (Pair prim/a b) [:Int v])` | qualified TYPE PARAM dies as incidental `module 'prim' … not found` at degenerate `0..0` span (the pre-S113 face, still live for this secondary binder; design §3.2 justified-excluded it to a /qa row that was never drawn) |

This is the coverage-by-definition-variants class: the S113/S114 binder matrix
drew the `/` column across all binder positions but never the `.` column, so
every position grew the same hole. The `deftype A.B` ctor-identity corruption
(`user/B`) is the sharpest face — `class=silent-accept` with a wrong minted
identity, sibling of the D-qual re-root class.

Also note the three-way document disagreement: spec §5 prose says dotted rejects
everywhere; the table's per-row Rule column says "qualified/dotted rejects" only
for type-params/con_var/`mod`/`platform` and bare "qualified rejects" for the
def-form heads and value-level locals; the design de-scopes `.` entirely
(Principle 6). One of the three must move.

## Proposed resolution

/qa draws the `{qualified `/`, dotted `.`} × binder-position` matrix rows
(positive twin: dotted ctor-pattern HEAD `Maybe.Some` stays legal — it is the
one deliberate dotted reference in pattern position, §6.2.1), attributes the
faces, and routes /testing pins. If /qa reads the spec table's per-row wording
as the narrower authority (locals: `/` only), the spec prose/table mismatch
routes to /spec for the user to settle; the design's falsified premise routes to
/design(frontend) either way. The mechanism fix (if ruled) is one predicate
widening at the shared helper + the `read_dotted_name`-fed head sites —
/dev(frontend), small.

## /qa disposition (S114 pre-W7, 2026-07-20 — matrix drawn; re-targeted /spec)

Record: `tests/plan/s114-test-plan.md` §11 item 3; the standing matrix is
**M3 in §5.1 of that plan** (the 0676 audit-R1 pattern — a row per binder
position × {`/`, `.`} × {reject, bare twin}, plus the deliberate §6.2.1
dotted ctor-pattern-HEAD positive, plus the never-drawn qualified-type-param
row from design §3.2).

- **Cell authoring = S115, not this sprint.** The spec three-way
  disagreement (prose "qualified OR dotted rejects everywhere" vs the
  table's narrower per-row wording vs the design de-scope) gates cell
  POLARITY for several rows; pins against a contested reading are
  wrong-polarity hazards (the S109 verify-example-well-formed lesson). The
  sharpest face — `(deftype A.B …)` minting ctor `user/B` — is a defect
  under EVERY reading (silent accept + corrupted minted identity), but its
  correct assertion (located reject vs coherent accept) differs by ruling,
  so it pins with the batch, first in the batch.
- **Routing (this FIXME re-targets down the chain, staying open):**
  1. **/spec** (now): frame the prose-vs-table disagreement for the user
     (§5 [S113] prose vs the per-row Rule column); the design's falsified
     premise is evidence, not authority — derive from the ruling, not the
     codebase.
  2. **/design(frontend)**: correct `binder-head-reject.md` §2's de-scope
     premise (falsified by probe) per the ruling.
  3. **/testing** (M3 batch) + **/dev(frontend)** (one predicate widening
     at the shared helper + the `read_dotted_name`-fed head sites; the
     M1/M2 structural criterion applies — ONE predicate, no per-position
     copies).

## Context

Found during /review of `8b2c3e20` (S114 W6 Track D) while checking the W-D2
value-level re-landing against the §5 binder table. NOT a regression of that
change-set — the predicate has been `/`-only since S113 W3 — but the wave that
completed the `/` column is the cheapest moment to have caught the `.` column,
and the spec MUST is live.
