# Module Preamble Capture (Reader)

Design document for Sprint 88, Phase 3, Step 3.2 — the frontend-reader mechanism
that captures the **leading comment-block module preamble** and produces its
stored text, per the user's comment-block model.

**Normative source:** `spec/08-modules.md §8.16` (the `[S88]` form, revised
2026-06-21 to the comment-block model). This doc is the *how* for the frontend's
slice of §8.16; the spec pins *what*.

**Storage target:** `cranelisp-types::SymbolTable.module_preamble: Option<String>`
(landed by `/arch`, FIXME 0428 — additive, `#[serde(default)]`, `CACHE_SCHEMA_VERSION`
8→9). The frontend produces the `Option<String>`; it does not own the field.

**Substrate:** `Sexp::Comment` (Sprint 24 — `design/frontend/comment-preservation.md`)
and the comment-preserving reader entry `parse_preserving_comments`
(`crates/cranelisp-frontend/src/reader.rs`).

---

## 1. Scope and boundary — where the frontend's responsibility ends

§8.16 spans three concerns; only the first is the frontend's:

| Concern | Owner | This doc |
|---|---|---|
| **Capture + extract** — recognize the leading comment block, strip markers, join → `Option<String>` | **frontend** (`/design`/`/dev` cranelisp-frontend) | §2–§4 below |
| **Wiring** — thread the captured text onto `SymbolTable.module_preamble` at module load | **int** (`src/`, the load seam) | §5 — frontend hands off; FIXME `target: /int` |
| **Regen re-emit** — re-emit the preamble verbatim as the leading comment block on source-regen | **int** (`src/save.rs`, the regen pretty-printer where 0423 lives) | §6 — frontend names the contract; FIXME `target: /int` |

The frontend's deliverable is a **pure function over the parsed sexp stream** that
returns the preamble text (or `None`). It performs **no** symbol-table mutation and
**no** file I/O. This keeps the frontend's "syntactic-only, pure" posture
(`design/frontend/s76-syntactic-only.md`; Principle 5 — testability is structural):
the capture function is unit-testable from a source string with no session.

---

## 2. Capture mechanism

### 2.1 The boundary rule (restated operationally)

Per §8.16.1, the preamble is the **contiguous block of line comments that begins on
the first line of the file and runs up to (but not including) the first form**,
**blank-line-terminated**. Operationally, walking the source from byte 0:

1. The block **starts at the first line**. If the very first non-whitespace token is
   not a `;` comment, there is **no preamble** (→ `None`). Leading blank lines before
   the first comment do **not** count as a blank-line break *before* the block has
   started (a file may open with a blank line then the comment block) — but see §2.4
   for the conservative ruling.
2. The block **accumulates** every contiguous comment line.
3. The block **terminates** at the first of:
   - **A blank line** (a line containing only whitespace between two comment lines, or
     after the comment run) — comments below the blank line are ordinary, never preamble.
   - **The first non-comment form** (`mod`/`import`/`export`/`platform` or any
     module-body form). The first form ends the block regardless of what follows.
   - **EOF** (a file that is *only* a comment block — the whole block is the preamble;
     a degenerate but valid case).
4. Comments appearing **after the first form** are never preamble (§8.16.1).
5. **At most one** preamble per module — the single contiguous leading block.

### 2.2 Why the existing `Sexp::Comment` stream is *not quite* sufficient as-is

`parse_preserving_comments` already surfaces leading comments as top-level
`Sexp::Comment` nodes in source order (§comment-preservation `Comment Positioning`).
A naive "take the leading run of `Sexp::Comment` nodes until the first non-comment
sexp" gets **most** of the boundary rule (rules 1, 2, 4, 5) for free — the
`Sexp::Comment` siblings already stop at the first real form.

The **one gap** is rule 3's **blank-line break**: the reader's
`skip_ws_collect_comments` (`reader.rs`) consumes whitespace — *including blank lines* —
silently between comments, so two `Sexp::Comment` nodes separated by a blank line are
indistinguishable in the stream from two adjacent comment lines. The span byte-offsets
*do* record the gap (the second comment's `Span.start` is past an intervening `\n\n`),
but reconstructing "was there a blank line between these two comments?" from spans alone
is fragile (it re-derives lexical structure the reader already saw).

### 2.3 Chosen approach — a dedicated capture pass with blank-line awareness

Add a small, **self-contained capture function** in the frontend that re-reads the
*head* of the source for preamble purposes, rather than overloading the
`Sexp::Comment` stream with a blank-line marker. Two implementable shapes; the doc
recommends **Shape A** (re-scan) for isolation, names **Shape B** (span-gap test)
as the cheaper alternative `/dev` may pick if the re-scan cost is ever a concern.

**Shape A (recommended) — head-of-source line scan.**

```
fn capture_module_preamble(source: &str) -> Option<String>
```

A direct line-oriented scan over `source` (independent of the full parse), reading
physical lines from byte 0:

- Skip nothing — start at line 1.
- For each line, classify: **blank** (whitespace only), **comment** (first
  non-whitespace char is `;`), or **form-start** (anything else).
- Accumulate comment lines until the first **blank** or **form-start** line (or EOF)
  terminates the run, per §2.1.
- If zero comment lines were accumulated before termination → `None`.
- Otherwise extract text (§3) from the accumulated comment lines and return `Some`.

This is a ~30-line pure scan with no dependency on the sexp tree. It is the most
faithful encoding of "the contiguous leading line-comment block, blank-line-terminated"
because it works in the same lexical units (physical lines) the spec's boundary rule
is written in. It is trivially unit-testable and cannot be perturbed by reader changes
to comment positioning inside forms.

**Shape B (alternative) — leading `Sexp::Comment` run + span-gap test.**

Reuse `parse_preserving_comments`; take the leading run of top-level `Sexp::Comment`
nodes that precede the first non-comment sexp; between consecutive comments, test
whether `source[prev.span.end .. next.span.start]` contains **two or more newlines**
(a blank line) — if so, truncate the run there. Cheaper (no second scan) but couples
preamble capture to span arithmetic over the comment stream, which is exactly the
fragility §2.2 flags. Acceptable if `/dev` prefers reusing the existing parse, but
Shape A is preferred on Principle 6 (the blank-line rule is the whole subtlety; encode
it where it is least error-prone).

**Whichever shape:** the function is **pure** (`&str -> Option<String>`), lives in the
reader module (or a sibling `preamble` module under `cranelisp-frontend/src/`), and is
re-exported at the crate root alongside `parse_preserving_comments`.

### 2.4 Corner cases (all resolved to a definite result)

| Source shape | Result | Rule |
|---|---|---|
| `;; doc` then `(mod m)` | `Some("doc")` | §2.1.3 first-form terminates |
| `;; line1`⏎`;; line2`⏎`(mod m)` | `Some("line1\nline2")` | contiguous run |
| `;; doc`⏎⏎`;; section`⏎`(mod m)` | `Some("doc")` | §2.1.3 blank-line break — `section` is ordinary |
| `(defn f [] 0)` (no leading comment) | `None` | §2.1.1 not a comment first |
| `;; doc`⏎`;; more` (EOF, no form) | `Some("doc\nmore")` | §2.1.3 EOF terminates |
| `;; a`⏎`(defn …)`⏎`;; b` | `Some("a")` | §8.16.1 `b` is after first form |
| empty file | `None` | no comment lines |
| leading blank line(s) then `;; doc` then form | **conservative: `None`** — see note | §2.1.1 ruling |

**Note on leading blank lines.** §8.16.1 says the block "begins on the first line of
the file." The strictest reading is: a blank first line means the comment run does
**not** begin on line 1, so there is no preamble. Shape A's scan as written (start at
line 1; a blank line *before any comment* terminates an empty run → `None`) yields this
strict result, which is the safe default — it never mis-captures a non-header comment as
documentation. If the user/`/spec` later wants leading blank lines tolerated, that is a
one-line relaxation in the scan (skip leading blanks before the run starts) and a
`target: /spec` clarification; the design notes it but does **not** assume it. **Flagged
as the single boundary ambiguity for the exit gate.**

---

## 3. Text extraction

Per §8.16.2, for each comment line in the captured block:

1. Strip the leading marker — `;;` or a single `;` — at the start of the line's
   non-whitespace content. (The reader's existing `try_read_comment` already strips a
   single `;` and one following space; the preamble scan must additionally tolerate the
   **`;;` double marker**, which is the idiomatic file-header form in the spec's own
   example. The rule: strip the maximal run of leading `;` characters that forms the
   comment marker, i.e. strip `;;` if present else `;`.)
2. Strip **one immediately-following space**, if present. (`;; Sudoku` → `Sudoku`;
   `;;Sudoku` → `Sudoku`; a bare `;;` line → `""`.)
3. Do **not** strip further whitespace — interior alignment/indentation after the one
   space is content and is preserved (round-trip fidelity, §6).

Join the stripped lines with a single newline (`\n`), preserving internal line
structure. A two-line block → a two-line string with one interior `\n`. No trailing
newline.

**Marker note (coordination with `comment-preservation.md`).** The existing
`Sexp::Comment` capture strips only a *single* `;` (`reader.rs::try_read_comment`).
The preamble's `;;` idiom means the preamble extractor's stripping rule is **marker-run
+ one space**, which is a *superset* of the single-`;` rule, not a conflict — Shape A
does its own line stripping and does not route through `try_read_comment`. If `/dev`
implements Shape B (reusing `Sexp::Comment` text), note that a `;;` comment currently
yields stored text `"; doc"` (one `;` plus the rest) — Shape B would therefore need a
second `;`-strip pass on the comment text. This is a further reason the doc recommends
Shape A (it owns the marker rule end-to-end).

---

## 4. Frontend public surface

One added pure function, re-exported at the crate root:

```rust
/// Capture the leading comment-block module preamble per spec §8.16.
/// Returns the joined, marker-stripped preamble text, or `None` when the
/// source has no contiguous leading comment block (the common, valid case).
/// Pure: no symbol-table mutation, no I/O.
pub fn capture_module_preamble(source: &str) -> Option<String>
```

- Lives in `cranelisp-frontend` (reader or a new `preamble` submodule).
- Additive to the frontend boundary — **one new `public-api.txt` line**. Per the
  baseline-diff discipline (`design/arch/CLAUDE.md` §"Baseline-diff discipline"),
  `/dev` regenerates `crates/cranelisp-frontend/public-api.txt` in the implementing
  change-set; `/design` (this doc + the master staleness row) records it.
- No change to `Sexp`, no change to `extract_module_declarations`, no change to the
  existing `parse` / `parse_preserving_comments` entries. The capture is **orthogonal**
  to structural-decl extraction — it reads the *raw source head*, not the peeled
  declarations.

**Why a standalone function, not a field on `ExtractedDeclarations`.** `mod_decls`
extraction already iterates the *parsed* (comment-stripped) `Vec<Sexp>` from the plain
`parse` path, where comments are gone (§comment-preservation: pipeline uses `parse`,
`preserve_comments: false`). The preamble needs the raw source (for blank-line
awareness and `;;` markers). Bolting it onto `extract_module_declarations` would force
that function to take `&str source` in addition to `&[Sexp]` — widening a narrow,
well-factored boundary (Principle 2) for an orthogonal concern. A separate function the
int load seam calls *alongside* extraction is the cleaner seam.

---

## 5. Association + wiring (frontend → int seam)

The frontend hands off; **int wires**. The seam:

- **Where modules are parsed for load.** int parses module source via
  `cranelisp_frontend::parse(&source)` at the load sites
  (`src/session_v4.rs:470`, `src/session_v4/lifecycle.rs:1029/1104`,
  `src/process_form/dependency.rs:412`), then calls `extract_module_declarations` and
  writes structural decls onto the per-module `SymbolTable` via
  `write_structural_decls` (Decision 33 — single source of truth for structural decls).
- **The added wiring.** At each module-load site, after parsing, int calls
  `cranelisp_frontend::capture_module_preamble(&source)` on the **same source string**
  and assigns the result to the module's `SymbolTable.module_preamble` (the field
  `/arch` added). This is one call + one field assignment per load site — no new
  control flow.
- **Frontend's responsibility ends** at returning `Option<String>` from the source.
  Threading it onto the right module's table, at the right load sites, in all modes
  (`--run` / `--link` / REPL / cache-restore), is int's orchestration concern — the
  same surface that owns `write_structural_decls` and the module-load lifecycle.

**Cache interaction (int's concern, noted for completeness).** `module_preamble` is a
serialized `SymbolTable` field (`/arch`: `#[serde(default)]`, schema 8→9), so a
cache-restored module carries its preamble through deserialization — int does **not**
re-run capture on a cache hit (the field is already populated). Capture runs only on a
fresh source parse. This mirrors how structural decls ride the cached table.

→ **FIXME `target: /int`** (§7) names this wiring obligation: call
`capture_module_preamble` at the load seam, populate `module_preamble`, do not re-capture
on cache restore.

---

## 6. Regen round-trip contract (coordination with FIXME 0423)

§8.16.5 requires the preamble to **round-trip byte-stably** through source-regen: a
module whose preamble is unchanged across a regeneration MUST emit a **byte-identical**
leading comment block (no reflow, re-wrap, re-indent, or re-mark).

### 6.1 The split — capture (frontend) vs. re-emit (int)

| Half | Owner | Site |
|---|---|---|
| **Capture** the leading comment block on read | frontend | `capture_module_preamble` (§2–4) — the input side of the round-trip |
| **Re-emit** the preamble verbatim as the leading comment block on regen | **int** | `src/save.rs::generate_module_source` — the output side, **where FIXME 0423 sits** |

`generate_module_source` (`src/save.rs:81`) is the regen pretty-printer: it assembles
sections (`mod` decls, platforms, imports, exports, traits, types, impls, fns/macros)
and joins them. **It is `/int`-owned**, and it is the **same path** FIXME 0423 is
correcting (CWD-relative backing-file write + annotation-spacing) for `(mod …)`
backing-file regeneration (§8.2.5).

### 6.2 The contract this design names

The preamble round-trip and the 0423 fix **share one regen pretty-printer path** and
MUST be reconciled there — not duplicated. The contract:

1. **`generate_module_source` gains a preamble-emit step as section 0** — *before* the
   `mod`-decls section — reading `symbol_table.module_preamble` and emitting it as the
   leading `;;` comment block at the file head (§8.16.5: canonical leading position,
   above the first form).
2. **Verbatim re-emit, no reflow.** The stored text is re-marked by prefixing each
   newline-split line with `;; ` (one space) and joining with `\n`. Because capture
   (§3) stripped exactly `marker + one space`, re-emit with `;; ` + line reproduces the
   canonical form. A preamble *captured from `;;`-marked source and not edited* must
   come back byte-identical — this pins the marker convention on **both** sides to
   `;;` + one space so capture/re-emit are inverse. (A bare-empty line → bare `;;`.)
3. **Set / clear** (§8.16.5): a module gaining a preamble inserts the block at the head;
   clearing (`module_preamble = None`) emits no section-0 block and MUST leave the rest
   of the file byte-stable.
4. **The 0423 fix and this emit step land on the one path.** Whoever resolves 0423
   touches `generate_module_source`'s write path; the preamble section-0 emit lands in
   the **same** function. The design's instruction to `/int`: **reconcile the preamble
   section-0 emit with the 0423 CWD/annotation-spacing fix in `generate_module_source`
   as a single change to the regen path** — do not stand up a parallel preamble-only
   regen helper that would drift from the 0423-corrected write.

### 6.3 Inverse-pair invariant (the testable contract)

The capture (§3 strip) and re-emit (§6.2.2 re-mark) rules are **inverse** on the
canonical `;;`-and-one-space form:

```
re_emit(capture(";; X\n;; Y\n(mod m)")) head-block  ==  ";; X\n;; Y\n"
```

This is the byte-stability acceptance criterion §8.16.5 demands. `/qa` can pin it as a
round-trip test (capture → store → regen → re-parse → capture again ⇒ same text;
*and* the head bytes are byte-identical). Noted as a testability requirement; `/qa`
authors the test.

→ **FIXME `target: /int`** (§7) names this regen obligation and the 0423 reconciliation.

---

## 7. Cross-skill handoffs (FIXMEs to file)

This design touches int's surface (the load-seam wiring and the regen re-emit). Per the
FIXME protocol, the frontend does not edit `src/`; it files for `/int`. One FIXME
covers both int-side obligations (they land on the same int surface, in the same Stage
B/Phase 5 window):

- **FIXME `target: /int`** — *Module-preamble wiring + regen re-emit.*
  - **Wiring (§5):** call `cranelisp_frontend::capture_module_preamble(&source)` at each
    module-load site (`session_v4.rs`, `lifecycle.rs`, `process_form/dependency.rs`) and
    populate `SymbolTable.module_preamble`; do not re-capture on cache restore.
  - **Regen (§6):** add a preamble section-0 emit to `src/save.rs::generate_module_source`
    that re-emits `module_preamble` verbatim as the leading `;;` block, reconciled with
    the FIXME 0423 fix **on the one regen path** (no parallel helper). Honour the
    inverse-pair invariant (§6.3) for byte-stable round-trip.
  - **Coordination:** explicitly cross-references FIXME 0423 — the preamble round-trip
    and the 0423 CWD/annotation-spacing fix MUST be reconciled in the same
    `generate_module_source` change.

(The numbered FIXME file is authored on the next `/sprint`-coordinated handoff per the
Step 3.2 brief; this doc names the contract content for that file. If filed standalone,
it takes `design/arch/fixmes/0429-int-module-preamble-wiring-and-regen.md` — 0429 being
the current `max+1`; `/sprint` resolves any collision at the wave gate.)

**Testability note for `/qa` (§4, §6.3):** unit coverage on `capture_module_preamble`
(the §2.4 corner-case table — each row is a unit test) lands with the frontend `/dev`
change; the byte-stable round-trip (§6.3) is an int/integration concern paired with the
0423 reproduction. No `target: /qa` FIXME is required — the test obligations are named
here and ride the owning skills' change-sets.

---

## 8. Quality attributes touched

| Attribute | Disposition |
|---|---|
| **Simplicity** (Principle 6) | One pure `&str -> Option<String>` function; the whole subtlety (blank-line break, `;;` marker) is encoded in one ~30-line line-scan, not spread across the sexp stream. No new `Sexp` variant, no `extract_module_declarations` widening. |
| **Testability** (Principle 5) | Capture is pure and session-free — the §2.4 table is a direct unit-test matrix. The round-trip (§6.3) is a named inverse-pair invariant. |
| **Maintainability** | The frontend↔int seam is one function call + one field write; the regen contract is one section-0 emit reconciled with 0423. Blast radius of a future preamble-format change is bounded to `capture_module_preamble` + the section-0 emitter (inverse pair). |
| **Narrow interfaces** (Principle 2) | The preamble concern does **not** widen the structural-decl extraction boundary; it is a sibling pure function the load seam calls alongside. |
| Concurrency / Performance / Observability | **Untouched.** Capture is a one-shot scan at parse time, off the hot pipeline path (the pipeline uses `parse`, which is unchanged); no concurrency surface. |

---

## 9. Cross-references

- `spec/08-modules.md §8.16` — normative module-preamble form (comment-block model, S88)
- `design/frontend/comment-preservation.md` — `Sexp::Comment` substrate + `parse_preserving_comments` (Sprint 24)
- `design/frontend/frontend.md §9` — staleness register (this doc added there)
- `design/frontend/s76-syntactic-only.md` — frontend's syntactic-only/pure posture
- `crates/cranelisp-frontend/src/reader.rs` — reader entries + comment capture (`try_read_comment`, `skip_ws_collect_comments`)
- `crates/cranelisp-frontend/src/module_extract.rs` — `extract_module_declarations` (the *orthogonal* structural-decl boundary; preamble is NOT bolted here)
- `src/save.rs::generate_module_source` — int-owned regen pretty-printer (the §6 re-emit site; FIXME 0423's home)
- `cranelisp-types::SymbolTable.module_preamble` — storage field (`/arch`, FIXME 0428, schema 8→9)
- `design/arch/repl-embedded-agent.md §3.4` — why first-class module preambles are load-bearing (agent memory model)
- `design/arch/CLAUDE.md` §"Baseline-diff discipline" — the `public-api.txt` regen obligation for the one added line
- `sprints/SPRINT.md` — Stage B preamble item; Step 3.2 brief
