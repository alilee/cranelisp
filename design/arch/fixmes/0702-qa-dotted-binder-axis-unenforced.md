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

---

## /spec framing for the USER (S115 Phase 3 — OPEN normative question; /spec frames, does not rule)

**The one question.** Does a **dotted (`.`) spelling** in a **binder** position —
`(defn a.b …)`, `(deftype A.B …)`, `(let [a.b 5] …)` — **reject** as a compile-time
error (exactly as a `/`-qualified binder already does), or is it **permitted /
left unspecified** in some binder positions? Three of our own documents disagree,
so one of them must move; only the user can say which.

### The three-way disagreement (spec prose vs spec table vs design + implementation)

- **Spec §5 PROSE (settled [S113]) is categorical.** "A binder … never carries a
  module qualifier (`/`, §1.4.3) **or a dotted path (`.`, §1.4.4)** … A **qualified
  or dotted** spelling in **any** binder position is a compile-time error." (§5
  intro, and again in the closing paragraph: "a `/`-bearing … **or `.`-bearing** …
  token is not a legal binder.")
- **Spec §5 TABLE per-row "Rule" column is narrower.** It spells out
  "**qualified/dotted** rejects" only for the two **type-variable** rows (`deftype`
  type parameters; `deftrait` con_vars) and "not qualified, **not dotted**" for
  `mod`/`platform`. For **every other** binder row — the `defn`/`deftype`/`deftrait`/
  `defmacro`/`impl`-method/`const`/`def` heads, the `deftype` ctor and field names,
  and **all** the value-level locals (`defn`/`fn` params, `let` names, `match`
  var-patterns, `import`/`export` rename aliases) — the Rule column says only
  "**qualified** rejects," **silent on `.`**.
- **Design + implementation de-scope `.` entirely.** `binder-head-reject.md` §2
  keys the reject on `/` **only** (Principle 6), on the premise "a dotted name …
  never appears in a raw declaration-head slot." That premise is **falsified by
  probe** — dotted binders reach the head slots and bind silently.

### Current behavior — the `{/, .}` × binder-position matrix

The `/` (qualified) column is enforced today and agrees across prose + table +
impl (`reject_qualified_binder_head` keys on `/`) — **one ragged cell**: a
qualified **type parameter** `(deftype (Pair prim/a b) …)` dies as an incidental
`module 'prim' … not found` at a degenerate `0..0` span, not a clean located
binder-reject (design §3.2 justified-excluded it to a /qa row never drawn). The
`.` (dotted) column is where behavior diverges from the categorical prose:

| Binder position | `.`-dotted current behavior | §5 prose | §5 table Rule column |
|---|---|---|---|
| `defn` head `(defn a.b [x] x)` | **silently binds** `user/a.b` | rejects | "qualified rejects" (silent on `.`) |
| `deftype` head `(deftype A.B [:Int v])` | **silently accepts**; type `user/A.B` but ctor **`user/B`** (identity corruption — head splits at `.`) | rejects | "qualified rejects" (silent on `.`) |
| `deftype` field `(deftype P [:Int a.b])` | **accepts** with a suppressed-accessor warning | rejects | "qualified rejects" (silent on `.`) |
| `deftype`/`deftrait` type-var (dotted) | (unprobed; `/`-qualified param dies incidental) | rejects | **"qualified/dotted rejects"** (spelled out) |
| value-level locals `(let [a.b 5] …)`, `(defn g [a.b] 1)`, `(match 1 [a.b a.b])` | all **silently bind** a dotted local | rejects | "qualified rejects" (silent on `.`) |
| `mod`/`platform` name | (unprobed) | rejects | **"not qualified, not dotted"** (spelled out) |

**Sharpest face:** `(deftype A.B …)` — a silent-accept that *also* mints a **wrong
constructor identity** (`user/B`), a corrupted downstream name.

**The positive twin that must stay legal under every ruling:** the dotted
constructor-pattern **head** `(Maybe.Some x)` (§6.2.1) is a **reference**, not a
binder — the one deliberate dotted spelling in pattern position. The var/call/type
**reference** positions (§8.5) likewise permit dotted. Any ruling here touches only
**binder** positions; the binder/reference line is where the rule is drawn, and the
user should confirm that is the intended cut.

### Candidate rulings

**Ruling 1 — the PROSE is authoritative: a dotted binder rejects in every binder
position (move the table + design + impl to the prose).** A `.`-bearing token in
any binder position is a **located compile-time error**, span on the offending
name, exactly as a `/`-bearing one. The `(deftype A.B …)` ctor-identity corruption
is closed at its root; the dotted field and dotted locals become clean rejects; the
qualified-type-param ragged cell is regularized to a located binder-reject at the
same time. Mechanism (small): widen the shared reject predicate from `/` to `/`-or-`.`
at the shared helper + the `read_dotted_name`-fed head sites; correct the table's
per-row Rule column to "qualified/dotted rejects" on every binder row (or state it
once in prose and stop per-row divergence); correct the design's falsified de-scope
premise. Reference positions (§6.2.1, §8.5) untouched.
- **Consistency:** matches the categorical §5 prose **and** the S114 reader rulings
  — `foo/`, `/bar`, `:foo/`, `a.b/` are all **located errors, never silent
  degradation** (§8.5.1, §2.4). A dotted binder is the binder-side sibling of that
  same "a malformed qualifier token is a located error" family. It is also the dual
  of §5's own binder principle ("you can define a name only into the module — or
  lexical scope — that contains the definition"): a dotted binder would be defining
  into a nested path, which the language has no notion of.

**Ruling 2 — the TABLE per-row wording is authoritative: `.` rejects only where the
table already spells it (type-vars, `mod`, `platform`); elsewhere a dotted binder is
permitted / unspecified (correct the prose downward).** This takes the table's
"qualified rejects" (silent on `.`) as the narrower authority and reads the prose's
"qualified **or** dotted, any position" as an over-statement to be softened.
- **The problem this ruling must answer:** the language has **no semantics** for a
  dotted binder. §5's settled principle forbids defining a name into another
  module/path, so `(defn a.b …)` — a binder naming a dotted path — has no coherent
  meaning; the current silent-bind (`user/a.b` as a flat name) and the ctor
  corruption (`user/B`) *are* that incoherence surfacing. So the honest form of
  Ruling 2 is not "dotted binders are a feature" but "leave the dotted-binder cells
  **unspecified/tolerated for now**" — a deliberate *movable-boundary park* (accept
  the current silent behavior, or at most improve the diagnostic, and revisit if a
  real use appears). That keeps the silent-accept + ctor-corruption faces as
  **accepted behavior**, which is almost certainly not intended, and it leaves the
  §5 prose contradicting the table until the prose is softened.
- **Consistency:** weaker — it re-opens a silent-degradation surface the S114 reader
  rulings deliberately closed on the reference side, and it requires editing the
  settled [S113] prose to be *less* categorical.

### /spec's neutral consistency note (analysis, not a ruling)

Under the settled §5 binder principle, **Ruling 1 is the only reading with coherent
semantics** — there is no notion of a binder that names a dotted path, so a dotted
binder can only be an error. The table's per-row silence on `.` looks like an
**incompleteness** (the S113/S114 waves drew the `/` column across all rows and
spelled `.` out only where a type-var/module row happened to mention it), not a
deliberate narrower rule — the coverage-by-definition-variants gap the FIXME names.
That said, whether to **reject** dotted binders now (Ruling 1) or **park** them
unspecified (Ruling 2) is a genuine normative choice the user owns; /spec will
scribe whichever the user rules (Ruling 1 → categorical reject stays and the table
+ design are aligned to it; Ruling 2 → the §5 prose is softened to the table's
narrower scope and the parked cells are documented as movable). A secondary point
the matrix surfaces regardless of the main ruling: the qualified **type-parameter**
cell `(deftype (Pair prim/a b) …)` currently rejects only *incidentally* (via
`module not found` at a `0..0` span) rather than as a clean located binder-reject —
a diagnostic-quality gap the user may want closed with whichever ruling lands.
