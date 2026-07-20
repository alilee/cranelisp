---
number: 0670
target: /dev
surface: src (int)
filed_by: /dev
filed_at: 2026-07-19
sprint_filed: 113
sprint: S114
refers_to: int macro-expansion name-resolution qualifies a VALUE-LEVEL local binder (defn/fn param, let name, match var) whose name collides with an importable symbol (`name` → `primitives/name`); this blocks the spec §5 value-level local-binder qualified-reject from landing at the frontend build layer
status: open
ruled: /arch 2026-07-20 (S114 Phase 3) — path 1; see §Ruling below
---

# int qualifies a local binder during macro expansion — blocks the §5 value-level local-binder reject

## RULING (/arch, S114 Phase 3, 2026-07-20) — path 1: fix int; a binder is never a reference

**The enforcement layer is the frontend build layer, unblocked by fixing the
int defect at its root**: int's macro-expansion qualification pass MUST skip
binder slots. A binder is never a reference — qualification is a
resolution-product operation, and a binder position produces no resolution
product (the same intent as Principle 24's corollary: only *references* carry
resolved identity; a binder *introduces* a name). The pass rewriting a binder
`name` → `primitives/name` is a correctness bug independent of the §5 reject
(a valid program gets a mis-qualified binder internally, masked only by the
consistent mis-qualification of the body reference).

**Path 2 (reader/raw-layer reject) is REJECTED as the mechanism**: it would
mask the int bug rather than fix it, and the spec's "structural at the reader"
claim it leans on is not as-built (the reader produces one
`Sexp::Symbol("a/b")` — no structural reject exists). The spec-accuracy
correction on that claim is filed as **FIXME 0683** (`target: /spec` — wording,
not semantics).

**Consequent chain (P2 F8 — three waves, strict order, Phase 4 places them):**

1. **int fix (this FIXME, now `target: /dev` src-surface, Track C):** the
   expansion-pass qualification skips binder positions — defn/fn params, `let`
   names, `match` var-patterns (the value-level binder slots §5 names). The
   binder-position enumeration must be COMPLETE across the walk (the 0660
   enumeration-completeness discipline applies: every binder-introducing form,
   or a legal skip, named in the change-set). Unit test at the expansion seam
   (`(defn greet [name] (str "hello, " name))` expands with the param BARE and
   the body reference qualified correctly) is mandatory per METHOD §2.2.
2. **Frontend value-level reject re-lands** at the three reverted seams
   (`build_annotated_params`, `build_let_bindings`, `build_pattern`) — now
   firing only on user-written qualified binders, never on int's output.
3. **`/testing` cells**: the positive cell (collision + macro compiles) + the
   value-level qualified-binder negative cells.

**Durable invariant recorded** at `design/arch/bounded-contexts.md` §6
(In-scope, macro-execution area): expansion-side name qualification operates
on references only; binder positions are never qualified.

## The finding (S113 W3, 0660(b)/item-3 implementation)

The user ruled all binder positions reject a qualified spelling (spec §5
binder-positions table). Implementing the reject at the frontend build-layer
seams surfaced a **pre-existing int-layer defect**: int's macro-expansion
name-resolution **qualifies a value-level local binder** whose bare name
collides with an importable symbol.

Minimal repro (workspace stdlib; a **valid** program):

```clojure
(defn greet [name] (str "hello, " name))   ; `name` is exported by trace; `str` is a macro
```

- `/expand` shows the param stays **bare** `name`:
  `(defn greet [name] (primitives/str-concat (show "hello, ") (show name)))`.
- But the **actual compile** rejects at the param with
  `'primitives/name' is a qualified name … a binder must be bare` — so between
  macro-expansion output and `build_form`, an int pass rewrites the **binder**
  `name` → `primitives/name`.
- Triggers ONLY when (a) the binder name collides with an importable symbol
  (`name`) AND (b) a macro (`str`) is in scope. `(defn greet [name] name)` (no
  macro) and `(defn greet [greeting] (str … greeting))` (no collision) both
  compile clean. `let` reproduces identically:
  `(let [name "x"] (str … name))` → same `primitives/name` reject.

This is an int name-resolution bug: it qualifies a **binder** as if it were a
reference (the exact thing the §5 ruling forbids). Before S113 it was **masked**
— the build-layer silently accepted the qualified param, and the body reference
was mis-qualified *consistently*, so the program ran.

## Why this blocks the frontend reject (and what I did in W3)

The spec §5 value-level local-binder positions — **defn/fn params, `let` names,
`match` var-patterns** — are parsed at `build_form`, which runs **after** int's
qualification pass. A qualified-binder reject there fires on **int's mangled
output**, not the user's source, so it **rejects a valid program**
(`(defn f [name] (str … name))`). I therefore **reverted** the reject at those
three seams (`build_annotated_params`, `build_let_bindings`, `build_pattern`) —
never ship a change that breaks a valid program — and left a NOTE at each.

**Landed in W3 (unaffected — earlier/raw layer, no regression):** the reject
DOES land at every binder seam that sees raw pre-int source:
`deftype` constructor names (both arms), `deftype` field names, `defmacro`
params (`parse_param_items` + `parse_bracket_pattern`), and the `import`/`export`
module alias (`module_extract`). Plus `mod`/`platform` (prior waves).

## Decision needed (arch — the enforcement-layer / paired-seam question)

The §5 ruling still owes enforcement at defn/fn-param, `let`, `match`. Two paths:

1. **Fix int** — stop qualifying binder-position symbols during expansion (a
   binder is never a reference; the qualification pass must skip binder slots).
   Then the frontend build-layer reject can land cleanly. This is the root-cause
   fix and the spec's model (a binder is bare where written). int-surface work.
2. **Enforce at the reader / raw-source layer** — the spec's own note says local
   binders "reject a `/`-bearing token structurally: the reader tokenizes `a/b`
   as a `qualified_symbol` … not the simple `SYMBOL` the binder grammar admits".
   Today the reader produces a single `Sexp::Symbol("a/b")` and does NOT reject,
   so this is not actually structural yet. A reader/raw-layer reject would catch
   a **user-written** qualified binder before int can mangle a legitimate one.

(1) is preferred — it fixes a real int correctness bug (mis-qualified binders)
AND unblocks the clean build-layer reject; (2) alone leaves the int bug (a valid
program still gets a mis-qualified binder internally). The paired-seam precedent
is FIXME 0650 (frontend reject + int span re-anchor). Route the int dispatch and
decide the enforcement layer.

## Test state

No pin owed from frontend (the reject is reverted, not failing). The int bug is
currently only observable via the two `repl_persist` e2e programs that name a
param `name` and use `str`; those are GREEN again after the revert. When int is
fixed (path 1), `/testing` adds a positive cell (`(defn f [name] (str … name))`
compiles) + the value-level qualified-binder neg cells the frontend reject will
then enforce.
