> [REPL specification index](index.md)

### 17.17 The `/syntax` Cheat-Sheet Command — Pillar 1 [S90]

S88/S89 made the agent *act*; the S90 fluency phase makes it *reach* for supplemental
detail rather than guess. The first reach is **`/syntax`** — a topic-indexed,
token-dense, **verified-compiling** reference for the **core language syntax**, surfaced
as a REPL command that is useful to **both the human at the prompt and the agent**
(the self-documenting-REPL principle — [root CLAUDE.md, Design Principles](../../CLAUDE.md#design-principles)
— turned toward syntax discovery). It is the curated, higher-precision replacement for fuzzy spec-grep
(`design/arch/repl-embedded-agent.md` §11 R7; the S90 plan's Pillar 1, `sprints/archive/sprint-90.md`). [S90]

**Ownership boundary (R7 — do not author content here).** This section specifies the
**command UX only**. The cheat-sheet **content** — the topic taxonomy and each topic's
verified-compiling examples — is **`/docs`-owned** (authored from `spec/`, validated by
`/spec`), shipped as a static `include_str!` asset (sibling to `primer.txt`,
`src/agent/`). The command-wiring (the `/syntax` `ReplCommand` variant + dispatch +
agent-tool allowlist row + the primer topic-name cross-reference) is `/dev (src/)`-owned.
`/syntax` **references** the topic vocabulary; it does **not** define it. [S90]

#### 17.17.1 The Two Forms — Bare List, Topic Detail [S90]

- **`/syntax` (bare)** — lists the **available topic names**, so a reader (human or agent)
  learns the vocabulary it can pull on. The output is a plain, scannable list of topic
  names (e.g. `hkt  defn-multi-sig  cond  match  traits  modules  annotations  let
  recursion-tco  …` — the exact set is `/docs`-owned). It MUST also name how to drill in:
  a one-line hint such as `Use /syntax <topic> for detail.` The bare list is the
  **index**, not the content. [S90]
- **`/syntax <topic>`** — returns that topic's **dense content**: a curated, mixed
  prose+form reference combining a compact explanation, syntactic **`FORM` templates**
  (e.g. `(defn name ([params] body) ...)` with `...` and metavariables), and one or more
  **verified-compiling** Cranelisp `EXAMPLE` lines. The asset is **rendered as authored —
  deterministic plain text, exactly the bytes shipped in the curated asset**. It is **not**
  routed through the S-expression pretty-printer: the `FORM` templates are syntactic
  skeletons, not parseable expressions, so the pretty-printer cannot consume them, and the
  concrete `EXAMPLE` lines are presented as-authored to preserve their layout. [S90 re-pin]
- **Unknown topic** — `/syntax <unknown>` MUST NOT error opaquely. It re-prints the
  available-topics list (as bare `/syntax` does) with a short note that the requested topic
  is not one of them — the self-documenting principle: a wrong topic name teaches the right
  vocabulary, never a dead end. [S90]

#### 17.17.2 Output Framing — Reuse Existing Roles, Degrade Cleanly [S90]

`/syntax` is **deterministic REPL output**, not agent prose — it is a static curated asset
read off disk, the same category as `/help` or `/list`. Accordingly:

- The topic's content is **emitted verbatim — deterministic plain text, exactly as authored
  in the curated asset**. It introduces **no new colour and no new style role**, and it does
  **not** route content through the pretty-printer or apply syntax highlighting to the
  example/form lines (§17.17.1). The bare-index headings and dim hints MAY use the existing
  §10.3 palette roles (the `/list`/`/help` family), but no new role is added. It is **not**
  wrapped in the `▌` agent-prose frame (§17.2) — that frame marks *model output*; `/syntax`
  content is curated, deterministic, and human-authored. [S90 re-pin]
- It **degrades under `--no-color`, `NO_COLOR`, or a non-TTY** (§10.1) to clean plain text
  with **no SGR codes** — the topic list reads as plain names, each topic's content as the
  authored plain text. Piped output and the showcase stay legible, exactly as `/list` does.
  Because the topic content is already plain text, `--no-color` and TTY output differ only in
  any framing (headings/hints), never in the body. [S90 re-pin]

> **Non-normative — possible future enhancement.** Syntax-highlighting the concrete
> `EXAMPLE` lines (the verified-compiling code) is conceivable later, but is **explicitly
> out of scope now**: the templated `FORM` lines are not parseable S-expressions, so the
> pretty-printer cannot render them, and the agent — the primary consumer — needs the dense
> text, not colour. Any future highlighting would have to discriminate `EXAMPLE` from `FORM`
> lines and would couple the renderer to the asset's content format; the modest gain does
> not justify it now. [S90 re-pin]

#### 17.17.3 Dual Use — Human Command and Agent Pull-Tool [S90]

`/syntax` is in the agent's **read-only pull allowlist** (§17.3) — the agent issues
`/syntax <topic>` to ground itself on a syntax point it does not know, exactly as it pulls
`/source` or `/info`. A pull issued to check syntax is a private probe under
§17.2.1: its command and result do not appear in the user session. The agent
shows its conclusions and any resulting code. A human-issued `/syntax` command
still displays the topic's dense, plain-text content. [S90] [S109]

**It is LLM-free.** `/syntax` is a static curated asset; it works **with the agent absent
or feature-off** — a human types `/syntax match` in a default (non-`agent`) build and gets
the cheat-sheet. (It is the agent's *pull surface* only when the agent is live; the command
itself is unconditional, like `/help`.) [S90]

#### 17.17.4 Relationship to the Primer Topic Cross-Reference [S90]

The always-on primer (`src/agent/primer.txt`) carries a **compact core-syntax summary that
cross-references the `/syntax` topic *names***, so the model knows *which topics exist* and
can pull detail on demand (R7; `repl-embedded-agent.md §11` item 1). The division of labour
the user experiences:

- the **primer** gives the model the always-needed essentials **plus the topic vocabulary**
  (a known list of names to reach for) — it does **not** inline every topic's full content
  (that would bloat every turn); [S90]
- **`/syntax <topic>`** is the **on-demand depth** the primer points at — pulled only for the
  few topics a given turn actually needs. [S90]

This is core-language syntax derived from spec — the primer-appropriate kind of grounding.
It does **NOT** hardcode prelude/stdlib idioms into the primer; those stay **harvest-sourced**
(§17.18, honouring the `agent-prelude-awareness-via-harvest-not-primer` ruling). The line:
**core syntax → primer summary + `/syntax` depth; prelude/stdlib symbols → harvest (§17.18)**.
[S90]

### 17.18 Ambient In-Scope Symbol Awareness — Harvest at Signature Grain — Pillar 2 [S90]

The harvester (§17.8, `design/arch/repl-embedded-agent.md §4.1`) already pushes the *shape*
of the session into every turn's context, silently and without being asked. S90 **enriches
its grain** so the agent has **ambient awareness of what is in scope** — the in-scope prelude
and imported symbols — at **name + full type signature + docstring** grain, every turn,
**without** the agent first having to spend a turn on `/imports`/`/list`/`/exports`. This is
the user-directed "keep prelude plus imported symbols in context" delivered the user-owned
way — **harvest, not primer** (`agent-prelude-awareness-via-harvest-not-primer`;
`sprints/SPRINT.md §Pillar 2`). [S90]

**This is ambient, not a command.** There is **no `/harvest` command** and nothing extra
appears in the human's REPL — the enrichment lives entirely in the context the agent
receives each turn (auditable offline via `/context`, §17.11, where it appears under
`=== HARVESTED CONTEXT ===`). The human-facing equivalents already exist and are unchanged:
`/imports` (§3.4) and `/list`/`/exports` (§3.3/§3.5) are how a *human* inspects in-scope
symbols; Pillar 2 gives the *agent* that same picture ambiently, at signature grain. [S90]

#### 17.18.1 The Display Grain — Name + Signature + Docstring [S90]

For each **in-scope** symbol — the current module's own definitions, the symbols the module
explicitly imports, **and** the implicit prelude symbols (the §3.4 "Prelude (implicit)"
surface when the prelude-fallback bit is on) — the harvested context surfaces **three facets
per symbol**:

1. **name** — the symbol as the agent would write it (bare when in scope; the reader already
   has the §3.4 import provenance), [S90]
2. **type signature** — the symbol's full type in the canonical cranelisp `:Type` notation
   (the same signature `/sig` and the bare-symbol lookup render, §4.1, §3.1) — fully-qualified
   type names, exactly as the REPL displays them, so the agent references the **actual**
   signature rather than guessing it, [S90]
3. **docstring** — the symbol's docstring when it has one (a defn docstring; a primitive's
   §A.5 Description, §3.1) — so the agent knows *what a symbol does*, not just its shape;
   absent when the symbol carries none (no placeholder). [S90]

This is **`/imports` + `/list` at signature grain** — the names those commands list, each
annotated with the signature and docstring a human would get by then typing the name. It is
a **read enrichment** of an existing harvest arm (the export-surface arm of `harvest_context`,
`src/agent/harvest.rs`) — the symbol table stays the single source of truth (Principle 7); the
harvest copies nothing, it reads grain it previously skipped. [S90]

#### 17.18.2 How It Reads In Context — and the Budget [S90]

The enriched in-scope block reads as a compact symbol-with-signature listing — conceptually
(the exact rendering is `/dev`-owned; this pins the grain and the read, not the bytes):

```
== in scope ==
solver/grid-get :: (Fn [primitives/Vec primitives/Int] primitives/Int)  ; Read a cell
+ :: (Fn [primitives/Int primitives/Int] primitives/Int)  ; primitive - integer addition
map :: (Fn [(Fn [a] b) (primitives/Vec a)] (primitives/Vec b))  ; apply f to each element
...
```

**Budget governs grain, as everywhere in the harvest (§17.8, `§4.2`).** Signature+docstring
grain is heavier than the bare export names §3.4 lists. The enrichment therefore rides the
**same graceful-degradation ladder** the harvester already enforces (`harvest.rs`, the
`char_budget` gate): under budget pressure the in-scope block degrades grain
(signature-without-docstring, then names-only) rather than being silently truncated to a
misleadingly-short list — the agent must never believe a symbol is *absent* merely because the
budget elided its detail. The acceptance is experiential: **a fresh agent session references an
in-scope symbol's actual signature without first having to `/list`/`/exports`** (`SPRINT.md
§Pillar 2 acceptance`). [S90]

### 17.19 Importable-Symbol Search — `/search` — Pillar 3 [S90 re-pin]

> **Status: current contract.** `/search` is a normal default-build session
> facility for public non-macro symbols. Source indexing does not execute macro
> expansion. Complete semantic indexing remains deferred in ACT-0952.

Pillars 1 and 2 ground the agent in the **core language** (`/syntax`) and **what is already
in scope** (harvest). Pillar 3 discovers searchable public non-macro symbols that are
**reachable but not yet imported** by **name and/or type signature**. This is the experience
of *"is there already a function that does this?"* answered **before** writing the `(import …)`,
for both the human and the agent. Macro declarations are deliberately outside this search
surface (§17.19.2a). [S90 re-pin]

**Reachable scope (R10).** The reachable modules `/search` indexes are the union of **two**
sources: (a) the **`.cl` modules on the lib search path ∪ the project root** — the same
file-resolution rules `import` uses; **and (b) the built-in seeded modules** — `primitives` and
the synthetic `macros` module — which have **no `.cl` file** and are instead present in the
session by bootstrap seeding. This second source is normative as of S108 (user ruling,
2026-07-11): the original R10 defined scope purely by file-resolution, so a real, importable
primitive such as `primitives/vec-len` was invisible to `/search` even though
`(primitives/vec-len [1 2 3])` evaluates. Public non-macro definitions in `primitives` MUST be
discoverable. [Tested tests/search::search_finds_seeded_primitive_offers_import] Eligible public
non-macro definitions in the synthetic `macros` module follow the same direct feed.
[Uncovered S121]

The reachable-module set does not make every declaration a search subject. Macro declarations
are excluded from every feed under §17.19.2a.

`/search`'s **primary** job is to surface search-eligible symbols that are **importable but not
yet in scope**: for these results, an `(import …)` form is the actionable payoff (§17.19.2).
Already-imported, in-scope symbols are otherwise surfaced by Pillar 2 (harvest, §17.18) and the
deterministic `/list` family. Consistent with R13, a seeded symbol is treated exactly like any other
reachable symbol: `/search vec-len`, where `vec-len` is **not** bare-in-scope, MUST surface
`primitives/vec-len` **with** the `(import [primitives [vec-len]])` payoff; were `vec-len`
already bare-in-scope, its exact-name row would instead be shown-but-marked *already in scope —
no import needed* (R13, §17.19.2). [Tested+Neg tests/search::search_finds_seeded_primitive_offers_import, tests/search::search_seeded_primitive_already_in_scope_marked_no_import]

**Exception — an EXACT-name match for a search-eligible symbol is always surfaced, even when
already in scope (R13, S106, FIXME 0543).** The original contract *dropped* an in-scope symbol
entirely, so `/search show` could list four tangential partial matches from an unimported module
while silently omitting the
exact match `show` that the user can already reference bare — the confusing outcome the user
reported. The rule is now: **an exact-name match for a search-eligible symbol MUST appear in the
results regardless of its scope status.** When that exact match is *already in scope*, its row is
**shown but marked** (§17.19.2) — labelled *already in scope — no import needed* instead of
offering an `(import …)` form. This preserves the "not-yet-imported" intent for the import-form
facet (an in-scope symbol truthfully needs no import) while never hiding the strongest match.
Partial (substring / prefix) matches keep the original behaviour — a partial match that is
already in scope stays excluded, as before; only the **exact** match earns the marked-but-shown
treatment. [S106]

**A normal session facility, not an agent feature (R9).** `/search` is an **ordinary
default-build REPL command** — it works in **every** REPL session, with or without the
`agent` feature. The background index that serves it is built by the **nice workers** (the
low-priority background threads that already do object-file codegen), which run regardless of
the `agent` feature. The agent reaches `/search` through the **ordinary
tools-as-visible-REPL-commands pull** (§17.3 / R11), exactly like `/syntax`, `/list`, or
`/exports` — there is **no special agent path** to it. The byte-identical-feature-OFF framing
that governs the agent-gated pillars (§17.1, §17.17) therefore does **not** apply to
`/search`: it is present and functional in the feature-OFF build. [S90 re-pin]

`/search` is served from a background index populated by a **typecheck non-macro forms → record
their public results → discard the typecheck state** sequence (`§11.1–§11.2`). To know a
**file-resolved** non-macro symbol's signature without importing its
module into the session, the indexer omits direct macro declarations, does not execute macro
expansion, typechecks the remaining forms in throwaway staging, reads the successfully checked
public non-macro definitions into derived lookup indices, and **discards** that typecheck state.
A failed non-macro indexing attempt contributes no rows from that source pass (§17.19.5).
[Tested+Neg src/session_v4/index_worker.rs::index_typecheck_mutates_no_live_shared_state, tests/search::search_ignores_macro_declaration_but_keeps_ordinary_definition_neg]

Because source indexing does not execute macros, `/search` does not promise definitions created
by macro expansion and may omit non-macro definitions whose indexing requires expansion. Actual
import is the authority for the complete compiled contents of a module; a partial search product
MUST NOT cause import to bypass normal macro compilation. A successfully loaded module or valid
compiled cache product MAY contribute its public non-macro definitions directly, but that does
not strengthen source-only `/search` into a complete semantic inventory. Full isolated
compilation, including macro typecheck, code generation, expansion, dependency loading, and
harvesting of expansion-produced definitions, is deferred; [ACT-0952](../../sprints/actions/ACT-0952-complete-semantic-search-indexing.md)
is its non-normative tracking record.
[Uncovered S121]

**The typecheck-then-discard dance applies only to file-resolved modules.** The built-in seeded
modules (`primitives` and the synthetic `macros` module; R10) are **already typechecked and
present** in the session's symbol table. They therefore need no staging typecheck or discard
step: the indexer reads their public non-macro definitions directly into the same name and scheme
indices, while excluding every macro declaration under §17.19.2a. An eligible result row
(§17.19.2) is indistinguishable in shape regardless of which feed produced it.
[Uncovered S121]

#### 17.19.1 The Command Shape — `/search <query>` [S90 re-pin]

`/search <query>` searches the indices described above and lists matching symbols. The
query is matched (per R6, `§11.4`) by either axis, **exact OR partial**:

- **by name** — `/search <name>`. **Exact** name match, plus **partial** = case-insensitive
  **substring** of the symbol name (e.g. `/search grid` finds `grid-get`, `grid-set`,
  `make-grid`); and/or [S90 re-pin]
- **by scheme** — `/search <scheme>`. **Exact** scheme match (the query type-shape matches an
  indexed signature **up to alpha-renaming of type variables**, e.g. `/search (Fn [Int Int]
  Int)` finds symbols of exactly that shape), plus **partial = structural-contains** — the
  query type-shape appears as a **sub-structure** of a candidate's scheme up to alpha-renaming
  (e.g. `/search (Vec Int)` matches a symbol of scheme `(Fn [(Vec Int)] Bool)`; `/search Int`
  matches any scheme mentioning `Int`). This structural-contains partial match is the target
  (`§11.4`); full Hoogle-style subsumption (a query `(Fn [Int] ?)` *subsuming* `(Fn [Int]
  Bool)` with hole-instantiation + ranking) is a **`/typecheck`-owned follow-up**, and the
  **query-pattern syntax for holes/wildcards** is a **flagged `/spec` consult** (R6, `§11.4`)
  — *not* specified here. [S90 re-pin]
- **by docstring** — `/search <text>`. **Case-insensitive substring** match against the
  symbol's docstring text (the first-line/summary and body captured for the symbol, the same
  text `/doc` shows). This closes the *"I remember roughly what it does but not what it's
  called"* case, which name/scheme matching cannot reach: a query that matches neither the name
  nor the signature but appears in the docstring MUST still surface the symbol. The docstring
  axis has **no exact/partial distinction** — it is always a substring test (a whole-docstring
  "exact" match is not a useful query shape). A symbol with **no docstring** simply cannot match
  on this axis. [S106, FIXME 0540]

How an implementation distinguishes a name query from a scheme query (e.g. a leading `(Fn …`,
or an explicit flag) is at implementation discretion, but the command MUST support **all three**
axes. The name and scheme axes MUST each support **both** exact and partial matching; the
docstring axis is always substring. A non-scheme-shaped query (plain text, no leading `(Fn …`)
is matched against **both the name axis and the docstring axis** — a single word can match a
symbol by name *or* by what its docstring says, and both kinds of hit are collected (then ranked
per §17.19.1a). An empty or no-match query re-prompts with a short "no importable symbols
matched" note (self-documenting; never an opaque error). [S90 re-pin] [S106]

##### 17.19.1a Relevance Ranking — Exact Before Partial, Name/Scheme Before Docstring-Only [S106]

Results MUST be ordered by **relevance**, not alphabetically (FIXME 0543 — the original
alphabetic `(module, name)` sort let a partial match like `trace-show-tree` precede an exact
`show`). The ranking is a **total order** applied across all collected hits, strongest first:

1. **Exact-name match** — the query equals the symbol name exactly (an in-scope exact match, per
   R13 above, ranks here too, carrying its *already in scope* marker). [S106]
2. **Exact-scheme match** — the query type-shape matches the symbol's scheme up to
   alpha-renaming (§17.19.1 "by scheme", exact). [S106]
3. **Prefix-name match** — the symbol name starts with the query (a partial-name hit that is
   stronger than an interior substring). [S106]
4. **Substring-name match** — the query appears elsewhere inside the symbol name. [S106]
5. **Structural-contains scheme match** — the query type-shape appears as a sub-structure of the
   scheme (§17.19.1 "by scheme", partial). [S106]
6. **Docstring-only match** — the query matched *only* in the docstring (name and scheme did not
   match). A **name/scheme hit outranks a docstring-only hit** — a name or signature match is a
   stronger relevance signal than a prose mention. A symbol that matches on *both* a
   name/scheme axis and its docstring ranks by its **best (name/scheme) tier**, not as a
   docstring-only hit. [S106]

**Tie-break within a tier:** results at the same relevance tier MUST fall back to the original
deterministic order — alphabetical by `(module, name)` — so output stays exactly reproducible for
testing (§17.19.5 determinism). [S106]

#### 17.19.2 The Result Row — Name, Signature, Module, How-To-Import [S90 re-pin]

**The row renders through the one canonical envelope (§1.1) — same shape as bare lookup / `/sig`
/ `/info` (S109, FIXME 0572).** A `/search` result row's **primary line** is the canonical
`:Type {name} ; {classification} - {docstring}` envelope (§1.1) — **byte-identical in shape** to
what a bare lookup, `/sig`, or `/info` of that non-macro symbol prints — followed by the
search-specific drawer lines (module column + import how-to). The row is **not** a fourth,
independently-formatted render of "what is this symbol"; it is the shared envelope constructor
(E4 seam, `design/arch/repl-styling-seam.md` §4) with the search drawers added. A row whose primary line
diverges from the envelope — for example, a `name :: (Fn …)` shape — is a conformance defect
against `01-display-format.md` §1.1, not a stylistic choice. Macro declarations produce no row
(`17a-agent-language-awareness.md` §17.19.2a). [S109]

Each result row MUST show enough for the reader to **decide and act** — these facets:

1. **symbol name** — the importable non-macro symbol, in the canonical envelope's subject slot;
   [S90 re-pin]
2. **type signature** — its full `:Type` signature (canonical cranelisp notation, FQ type
   names, §4.1) occupying the envelope's `:Type` slot — the same grain Pillar 2 surfaces for
   in-scope symbols, so search results and in-scope listings read identically. For a constructor
   or type, the `:Type` slot holds what bare lookup holds (§1.1/§4.1). Macro declarations are
   excluded rather than assigned a placeholder scalar (§17.19.2a); [S90 re-pin] [S109]
3. **originating module** — the module the symbol lives in (its full path), so the reader knows
   *where it comes from*; [S90 re-pin]
4. **how to import it** — the exact `(import …)` form that would bring it into scope (e.g.
   `(import [solver.grid [grid-get]])`) — so a human can copy-paste it and the agent can
   propose-and-submit it (Build mode, §17.14) directly. This is the actionable payoff:
   search → see the form → import. **For an exact-name match that is already in scope** (R13,
   §17.19), this facet is **replaced** by the marker `already in scope — no import needed`
   instead of an `(import …)` form: the symbol is usable bare, so no import is offered, but the
   row is still shown (never hidden). [S106] [S90 re-pin]
5. **why it matched, for a docstring-only hit** — when a result was surfaced **only** because
   the query appears in its docstring (name and scheme did not match — §17.19.1a tier 6), the
   row MUST include a short **excerpt** showing the matched text in context (a snippet of the
   docstring around the matched substring, e.g. `… computes the greatest common divisor …` with
   the matched span), so the reader is not left guessing which docstring hit fired. This facet
   appears **only** on docstring-only rows — a name/scheme hit does not need it (the name or
   signature already shows the reason it matched). [S106, FIXME 0540]

Conceptually (rendering `/dev`-owned; this pins the facets and the canonical-envelope primary
line, §1.1):

```
user> /search (Fn [Int Int] Int)
:(Fn [primitives/Int primitives/Int] primitives/Int) grid-get ; defn - Read a cell
  in solver.grid   — (import [solver.grid [grid-get]])
:(Fn [primitives/Int primitives/Int] primitives/Int) gcd ; defn
  in math.number   — (import [math.number [gcd]])

user> /search show
:(Fn [:Display a] primitives/String) show ; defn - Format as string
  in text.display   — already in scope — no import needed
:(Fn [primitives/Trace] primitives/String) trace-show ; defn
  in core.trace   — (import [core.trace [trace-show]])

user> /search "greatest common"
:(Fn [primitives/Int primitives/Int] primitives/Int) gcd ; defn
  in math.number   — (import [math.number [gcd]])
  ; doc: … computes the greatest common divisor of two integers …
```

The first example shows scheme matches; the second shows the exact-name match `show` surfaced
**marked** as already in scope (R13), ranked above the partial `trace-show` (§17.19.1a); the third
shows a docstring-only hit (`gcd`'s name and signature contain neither word) carrying its excerpt
facet. Results use the **existing §10.3 palette roles** (the `/list` family) — the docstring
excerpt line uses the **dim `; ` metadata role** (the classification-comment / metadata role,
§10.3 R6 — a `; doc:` excerpt is REPL-emitted structure, not user source, so dim not italic) —
and **degrade under `--no-color`/non-TTY** (§10.1) to clean plain text, same rule as `/syntax`
(§17.17.2) and every other deterministic command. [S90 re-pin] [S106]

##### 17.19.2a Macro Declarations Are Not Search Subjects [Tested+Neg tests/search::search_ignores_macro_declaration_but_keeps_ordinary_definition_neg, src/session_v4/index_worker.rs::public_table_projections_omit_macro_groups]

`/search` MUST ignore macro declarations from every source, including a valid cache, an already
loaded module, and the compiler-seeded `macros` module. The exact-name-in-scope exception in R13
does not apply to a macro. `/search` MUST NOT create a macro result row, assign a macro a
placeholder type, or retain declaration-only macro metadata in the search indices. This exclusion
applies only to `/search`: an imported or locally defined macro remains available through the macro
introspection surfaces in §11.2.

##### 17.19.2b A Constructor Is Listed Once, Under Its Canonical `Type.Ctor` Form [S109]

With the dotted-`Type.Ctor` constructor capability (`sprints/SPRINT.md` bucket 2 — same-named
constructors coexisting across types, minting a canonical `Type.Ctor` key plus a bare-name alias),
a constructor now has **two** symbol-table entries: the canonical `Maybe.Some` and the bare alias
`Some`. `/search` MUST surface a constructor **exactly once**, under its **canonical qualified
`Type.Ctor` form** (`Maybe.Some`, `Color.Red`) — **never** as two rows (`Maybe.Some` *and* a
separate bare `Some`). This **mirrors the field-accessor rule** (§3.3 / §3.5 — canonical
`Type.field` shown once, bare alias not separately listed; FIXME 0438) and the same rule now
applies to `/list` (§3.3) and `/exports` (§3.5): the bare ctor name is a **convenience alias** (import
class), not a second importable definition, so it is not a second search row. The row's import
how-to targets the constructor's home type/module as usual. A search that double-lists a
constructor once canonically and once bare is a conformance defect against this rule. This couples
with the value-display side (§1.5): the value `Maybe.Some 3` renders `(Maybe.Some 3)` in the
canonical dotted form, and its `/search`/`/list` rows name it the same canonical way — one identity,
one listing. The canonical-once rule is guarded on the `/list` face (each constructor listed once
under its `Type.Ctor` form, no bare-alias second row); because `/search`/`/list`/`/exports` render
through the shared canonical renderer (§1.1), the rule holds across the sibling surfaces by
construction. [Tested tests/repl_introspection::list_types_includes_constructor_rows_under_canonical_dotted_form, tests/repl_introspection::list_shows_ctor_once_canonical]

#### 17.19.3 Eager Background Index — Partial Results While Indexing [S90 re-pin]

The background index is **eager** (R4/R9b): the nice workers **arm** it at **REPL startup** — as
soon as the session begins, before any `/search` is issued or the agent is activated — and once
armed they **race ahead**, burning down the reachable-module worklist eagerly, not one module per
query. (Startup arming is normative as of S108, reconciling the spec with the implementation in
`main.rs`; it supersedes the earlier **eager-but-triggered** model in which arming waited for the
first `/search` or first agent activation. The reachable-module burn-down now begins with the
session so the index is warm as early as possible.) [Tested tests/search::search_burndown_arms_at_repl_startup_neg_not_on_first_search]

Because the burn-down may still be in progress when a `/search` lands, the experience contract
is **partial-results-plus-a-note**: a `/search` issued before indexing completes MUST serve
the matches found **so far** and append a short progress note — **`indexing N module(s)… (results
may be incomplete)`** — telling the reader the result set is incomplete and more may appear if the
search is repeated. The `module(s)` form carries the singular/plural agreement (one pending module
reads `indexing 1 module…`), and the trailing **`(results may be incomplete)`** clause makes the
partial-results contract explicit in the note itself.
**`N` is the count of reachable modules still pending** (armed-but-not-yet-burned-down) at the
moment the search is served — the size of the remaining worklist, not the total or the
already-done count — so the reader sees how much index is still outstanding and it counts down
to zero as the burn-down advances. The note MUST be served whenever the index is not yet
complete, **even when the partial result set is empty**: an empty-but-still-indexing search
serves the `indexing N module(s)…` note and **not** the `no importable symbols matched` note
(§17.19.1) — the two are distinct states and MUST NOT be conflated, because "nothing matched a
complete index" and "nothing matched yet because the index is still building" call for opposite
reader actions (rephrase vs. simply retry). This is the same self-documenting, never-opaque
posture as every other deterministic command: a not-yet-complete index is a transient state
surfaced plainly, never an error and never a silent empty result. A subsequent `/search`, once
the burn-down has advanced, returns the fuller set. [S90 re-pin] [Tested tests/search::search_seeded_file_name_collision_does_not_wedge_pending_note — e2e pins the no-wedge/absence-after-settle path; the note-fires and empty-partial non-conflation MUSTs are unit-pinned (src/repl/search.rs::indexing_note_text_present_iff_pending, src/repl/search.rs::empty_result_still_indexing_serves_only_the_note_not_no_match, src/repl/search.rs::empty_result_complete_index_serves_only_no_match_not_the_note) — the fire path is timing-coupled, not e2e-deterministic (S108)]

**Completion message — `; search index complete.` (S108).** When the background burn-down
finishes — every reachable module source (file-resolved + seeded) processed under the current
non-macro indexing contract, and the pending worklist drained to zero — the REPL emits a single
one-line notice: **`; search index complete.`** Completion reports worklist exhaustion; it does
not promise that macro declarations or expansion-produced definitions were indexed (§17.19.2a).
This closes the lifecycle the `indexing N module(s)…` note (above) opened: a reader who was told
the index was still building learns, without having to re-issue `/search` and inspect whether the
count reached zero, that a repeat search now sees the full set available under the current
non-macro contract. The wording is fixed: the literal lower-case sentence
`search index complete.` prefixed with the REPL comment marker `; ` — rendered as
`; search index complete.`, a classification-comment line (§10.3) consistent with every other
`;`-prefixed REPL meta-line — with a trailing period and no count (the count belongs to the
*in-progress* note; completion is a binary state).
[Tested src/session_v4/index_worker.rs::take_completion_notice_requires_pending_zero, src/session_v4/index_worker.rs::take_completion_notice_one_shot_gated_on_note_shown]

**When it fires (settled — user ruling 2026-07-11 via `/sprint`).** The completion notice fires
**only when a prior `indexing N module(s)…` not-ready note was shown to the user in this session**
(**option (b)**) — i.e. completion speaks only to close a loop the user actually saw open. If no
`/search` ever ran before the burn-down finished (or every `/search` happened to land after
completion), the session was never told the index was building, so a "complete" notice would
announce the end of a process the user never observed beginning — noise. Option (b) is quieter than
**(a) always announce completion on every session** (which pays a line of noise even for sessions
that never search) and more immediate than **(c) surface completion only on demand, echoed by a
subsequent `/search`** (which never proactively closes the loop and forces a re-issue to learn the
index is ready). The user settled on (b); the **wording** above (`; search index complete.`) and
the async-delivery constraints (below) stand. [Tested src/session_v4/index_worker.rs::take_completion_notice_one_shot_gated_on_note_shown — unit; the timing-(b) `note_shown` gate is deterministic at the `IndicesInner` seam, async at the REPL surface so no e2e (S108)]

**Async-delivery constraints (both messages).** `indexing N module(s)…` is emitted **inline** as
part of the `/search` result the reader requested, so it carries no special async concern. The
`; search index complete.` notice is different: it is emitted **asynchronously** from the
background nice-worker burn-down, not in direct response to a keystroke, so it MUST obey the
same two invariants every other async surface honours. **(1) No mid-line interleave.** The
notice MUST NOT be written while the user is mid-line composing input — it MUST be emitted only
at a clean line boundary (between a completed prompt cycle and the next prompt), never splicing
bytes into a line the user is typing; the async writer coordinates with the line editor exactly
as §10.8's interactive line-editor contract requires, so the input buffer is never corrupted.
**(2) Colour gate + non-TTY byte-identical.** The notice honours the **global** colour gate
(§10.1, §10.7) — dim styling (the classification-comment / metadata role, §10.3 R6) when colour is enabled,
and under `--no-color`/`NO_COLOR`/non-TTY it degrades to clean plain text with **no** SGR codes,
via the same single global gate every styled line uses, never a separate one. On a **non-TTY**
session there is no interactive line editor and no armed-then-watched burn-down the user waits
on; the notice MUST NOT perturb the byte-identical scripted/piped-output contract (§10.8) — a
non-interactive `/search` invocation's captured bytes stay exactly as they are without the async
notice. [Tested src/repl_input.rs::piped_input_is_not_interactive_so_completion_notice_is_gated_off — unit; the non-TTY byte-identical gate (I-3). The no-mid-line-interleave invariant is structural (the notice is polled only at the main.rs prompt boundary), no separate e2e (S108)]

#### 17.19.4 Dual Use — Human Command and Agent Pull-Tool [S90 re-pin]

`/search` is both a **human REPL command** (typed at the prompt to find a library function
before importing) and an **agent read-only pull-tool** (§17.3) — the agent issues `/search …`
to discover a reachable search-eligible symbol it needs, exactly as it pulls `/syntax` or
`/exports`, through the same ordinary REPL command surface (R11);
there is no agent-specific search path. A pull issued to discover a symbol is a
private probe (§17.2.1): its command and result are not echoed into the session.
The agent shows the conclusions and proposed code. The command is a
**normal default-build facility** (the index is deterministic and built by the nice workers;
the command works with the agent absent — §17.19 preamble, R9). The natural agent workflow the
dual use enables: *search → find the symbol + its import form → propose the import (and the
using code) through the Build confirm-gate (§17.14)* — fluency end-to-end, from "is there a
function for this?" to a submitted, importing, type-checking form. [S90 re-pin]

#### 17.19.5 Robustness — Searching the Library Must Never Crash the REPL [S90 re-pin]

Because Pillar 3 parses and typechecks the non-macro forms of **arbitrary reachable third-party
modules** at index time, a malformed or otherwise invalid reachable module on the lib-path ∪
project-root could crash a worker if indexing were not contained (`§11.3`). **`/search` MUST NOT
crash the REPL or the session**, and indexing MUST NOT silently degrade the session, regardless
of what a reachable module contains. If parsing, declaration processing, building, or the
non-macro typecheck fails — including when a remaining form cannot be checked without macro
expansion — that source-index attempt contributes no rows. The failure is never an unwound worker
thread, a panic, or a lost session; it MAY be recorded or surfaced as a search-quality note such
as `could not index <module>`, but MUST NOT be presented as a language error from `/search`.
[Tested+Neg tests/search::search_cf2_unindexable_module_skipped_no_crash, tests/search::search_cf2_neg_no_killed_worker_no_meta]
