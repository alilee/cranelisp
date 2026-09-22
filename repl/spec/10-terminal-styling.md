> [REPL specification index](index.md)

## 10. Terminal Styling [R4 S22]

When connected to a colour-capable terminal, the REPL MUST apply ANSI styling to distinguish output categories. Styling makes the `:Type value` format scannable — the type prefix, the value, and the classification comment are visually distinct without requiring the user to parse punctuation.

### 10.1 TTY Detection and Suppression [R4 S22]

Colour MUST be enabled by default on capable terminals and suppressed otherwise. The detection logic, in priority order:

1. **`--no-color` flag**: If the `--no-color` CLI flag is present, all ANSI output MUST be suppressed. This flag MUST be accepted alongside other flags (e.g., `cranelisp --no-color`, `cranelisp --run file.cl --no-color`).
2. **`NO_COLOR` environment variable**: If `NO_COLOR` is set to any non-empty value, all ANSI output MUST be suppressed (per https://no-color.org). The value is irrelevant — `NO_COLOR=1`, `NO_COLOR=true`, and `NO_COLOR=` (empty) all suppress except the empty string case: `NO_COLOR=` (set but empty) does NOT suppress.
3. **TTY check**: If stdout is not a terminal (`!isatty(stdout)`), all ANSI output MUST be suppressed. This covers piped output (`cranelisp | less`), redirected output (`cranelisp > log.txt`), and batch mode (`--run`).
4. **Otherwise**: Colour is enabled.

There is no `--color=force` flag. If a user needs colour in piped output (e.g., for `less -R`), they can use a tool like `unbuffer` or `script`. Keeping the implementation simple is more important than covering this edge case.

### 10.2 SGR Escape Convention [R4 S22]

All styling uses ANSI SGR (Select Graphic Rendition) sequences only — no cursor movement, no alternate screen, no 256-colour or truecolor. The palette is restricted to the base 8 colours (30-37) plus bright variants (90-97) and attributes bold (1) and dim (2). This ensures legibility across all terminal emulators, including the macOS default Terminal.app which has limited truecolor support.

Every styled span MUST be terminated by a reset (`\033[0m`) before any newline or before transitioning to a differently-styled span. Unterminated escape sequences corrupt subsequent output and are a conformance failure.

Escape sequences MUST NOT appear inside the value portion of `:Type value` when that value is a String literal — the string content is user data and MUST be printed verbatim.

### 10.3 Token/Element Styling Contract — The One Styling Authority [S108]

This subsection is the **single normative authority** for the element → style-role mapping across **all token-styled REPL output**: result values (§1.2/§1.5), introspection lines (§4.1 — `/sig`, `/info`, bare-symbol lookup), pretty-printed code (§3.11 — `/sexp`, `/source`, and the agent ```lisp blocks §17.13.2 routes through the same printer), `/search` result rows (§17.19.2), and error/warning lines (§5). Every byte of token-styled output derives its style from **exactly one** role in the table below; a role is defined once here and applied once at render, so styling cannot drift between surfaces. The per-surface style descriptions that predate this table (§1.1/§1.5 value styling, §3.11 "colour on adds SGR spans", §4.1 introspection styling, and the §10.4 worked illustration) are **subordinate** to it and cross-reference it — **this table wins on any conflict.** There are no user-configurable themes; the defaults work on both light and dark backgrounds using the standard 16-colour ANSI palette. [S108]

**Scope boundary — the layout family is out of styling scope (user, 2026-07-12).** The pure symbol-list **name bodies** of `/list`, `/imports`, and `/exports` (§3.3) are a uniform-**layout** concern, not a token-styling one — their names are default-styled and their layout is governed by §3.3 L0–L4. Only their **category headers** carry a styling role (R12, below), applied through this same contract. `/search` rows DO carry token roles (`:Type`, module path, import snippet) and are **in** scope. [S108]

**The role table (byte-reproducible).** The **SGR** column is the exact Select Graphic Rendition parameter string emitted between `\033[` and `m`. Every styled span is terminated by a reset `\033[0m` per §10.2 before any newline or transition to a differently-styled span.

| # | Role | Elements it covers | Style | SGR |
|---|---|---|---|---|
| R1 | Head | The **head of an apply form** — the first symbol of a `(…)` list in operator position (pretty-printed code only, §3.11); includes the delimiter when a nested form sits in head position. | bold | `1` |
| R2 | LitNumBool | Integer, float, and boolean **literals** — in pretty-printed code **AND** in result-value display (§1.2/§1.5). | yellow | `33` |
| R3 | LitStr | **String literals** — in code **AND** value display. The span wraps the whole quoted literal `"…"` as one unit; per §10.2 **no SGR is ever emitted inside the string content** (user data, printed verbatim). | green | `32` |
| R4 | TypeAnnotation | A **type annotation** — `:Type`, `:module/Type`, `:(Fn […] …)`, `:(prelude/Option a)` — wherever it appears (result lines, introspection lines, search rows, code). Styled cyan **as a single construct**: a `module/` prefix *inside* an annotation is part of the one cyan span and is **NOT** separately dimmed (user ruling 2026-07-12 — no internal decomposition inside type annotations). | cyan | `36` |
| R5 | SourceComment | A `;` **source-code comment** in pretty-printed code — a comment the *user wrote in their own source*, surfaced by `/sexp`/`/source`/agent ```lisp blocks. | italic | `3` |
| R6 | ReplMetadata | A **REPL structured-metadata `;` line or suffix** — the classification comment (`; defn`, `; deftype`, `; deftrait`, `; special form`, `; primitive`, `; impl`), the related-symbol drawer headers and their name bodies (`; match:`, `; defn:`, `; impl:`, and the names beneath), `; doc:` excerpts, the `; warning:` prefix, and lifecycle notes (`; indexing N module(s)…`, `; search index complete.`). These are **not comments in the source-code sense** — they are REPL-emitted structure. | dim | `2` |
| R7 | ModulePrefix | The **`module/` prefix on a bare fully-qualified symbol NAME** — `collections.vec/` in a `collections.vec/count` name, the module column of a `/search` row. Applies to FQ **names**; it does **NOT** apply inside a type annotation (a `module/` within `:module/Type` is R4 cyan). | dim | `2` |
| R8 | ErrorKeyword | The `Error:` keyword and equivalents (`runtime error:`). | bold red | `1;31` |
| R9 | ErrorDetail | The error message body. | red | `31` |
| R10 | WarnKeyword | The `Warning:` keyword. | bold yellow | `1;33` |
| R11 | WarnDetail | The warning message body. | yellow | `33` |
| R12 | Header | A slash-command **category header** — `Fns:`, `Types:`, `Traits:`, `Special forms:`, etc. (the one styling role the layout-family lists carry). | bold | `1` |
| R13 | Prompt / Banner | The prompt line (timing + module + `>`, §2.1) and the startup banner (§6.2). | dim | `2` |
| R14 | AgentGutter | The agent prose frame `▌` gutter (§17.2). Only **prose** is guttered; echoed agent-issued commands, their results, and agent-emitted ```lisp code blocks render un-guttered in their own roles (§17.2 item 3, §17.13.2, FIXME 0556). A probe is not rendered at all, so it takes no role here (§17.2.1). | bright magenta | `95` |
| R15 | Name / Plain | **Everything else** — the non-prefix part of symbol names, constructor dot-names (`Color.Red`), `<closure>`, vec/list/bracket punctuation, whitespace, and layout padding. | default | — |

**Composite — the `agent>` input prompt (§17.12).** The `agent>` glyph shown when the agent "types" a line is a composite of R13 (Prompt, dim) over the line with the `agent` token in the R14 bright-magenta colour — expressed as R13 + R14-family spans over the same line. It marks who issued each echoed line (distinct from the dim human prompt §2.1 and the `▌` prose gutter); a probe is not echoed and carries no `agent>` line (§17.2.1). It degrades under colour-off to the plain token `agent>`. [S108]

**Normative requirements.**

- **(1) Completeness — exactly one role per byte.** Every byte of token-styled output MUST derive its style from **exactly one** role above. A surface that needs a role not in this table is a **spec change** (bring it to `/repl` and the user), never an implementation choice. This is what makes "define once, apply once" enforceable and drift structurally impossible. [S108]
- **(2) Colour-off is byte-identical regardless of role — one global gate.** When colour is disabled (§10.1 — `--no-color`, `NO_COLOR`, or non-TTY) the output MUST be **byte-identical to the role-free plain text** for that line: the concatenation of the spans' text content, with **no SGR whatsoever**. Role assignment MUST NOT change layout, spacing, column positions, or any byte other than the SGR escapes. This one global colour gate is the guarantee behind the non-TTY goldens and the agent `strip_ansi` membrane (§17) — a role that perturbs plain-text bytes is a conformance failure. [S108]
- **(3) Colour-on adds only SGR spans at the same columns — determinism.** With colour on, rendering MUST add **only** SGR spans wrapping the same characters at the same columns the colour-off output produces (the §3.11 layout-determinism discipline, extended from layout to styling). For a fixed input, colour-on output is byte-for-byte reproducible: the same roles at the same offsets every time. `/qa` pins each output kind against a colour-on byte-exact fixture. [S108]

**FIXME 0561 resolution — source comments italic, REPL metadata dim (two distinct roles).** A `;` **source-code comment** (R5) renders **italic** (`\033[3m`); a REPL **structured-metadata** `;` line (R6 — `; defn`, `; match:`, `; impl:`, `; defn:`, the classification and related-symbol drawers, `; doc:` excerpts, and lifecycle notes) renders **dim** (`\033[2m`). They are **different roles** with different styles: the R6 metadata `;` lines are REPL-emitted structure ("not comments in the source-code sense" — the standing note below), whereas an R5 comment is text the user wrote in their source. The pre-S108 divergence (the code highlighter over-applied italic to the metadata role while the spec said dim) is resolved by this split: **metadata = dim (R6); source comment = italic (R5)**. This closes FIXME 0561. [S108]

Notes on specific choices:

- **Green is for string literals, not comments.** An earlier draft used green for `;` comment lines; comments are now italic (R5, source) or dim (R6, metadata), and green (R3) is reserved for string literals. REPL metadata `;` lines carry structured information (classifications, related symbols) — they are **not** comments in the source-code sense, so dim (not a saturated colour) keeps the visual hierarchy: type = cyan, literal = coloured, metadata = dim.
- **Bold for structural anchors only.** Bold (R1, R8/R10 keyword prefixes, R12) is reserved for the head of an apply form, error/warning keywords, and category headers. Using bold elsewhere dilutes its signal.
- **No colour on user input.** The line editor controls input styling. The REPL MUST NOT emit escape sequences into the input buffer.

### 10.4 Styled Universal Output Format — Worked Illustration [R4 S22]

This subsection **illustrates** the §10.3 contract applied to the universal output format (§1.1); **§10.3 is the authority** and wins on any conflict. Angle brackets show styled spans annotated with their §10.3 role; actual output uses SGR codes, not brackets.

**Expression result** (the literal value is R2 yellow — not default):
```
<cyan R4>:primitives/Int</cyan> <yellow R2>42</yellow>
```

**Definition with classification and docstring** (the `user/` name prefix is R7 dim; the type annotation is one R4 cyan span; the classification comment is one R6 dim span):
```
<cyan R4>:(Fn [primitives/Int] primitives/Int)</cyan> <dim R7>user/</dim>double <dim R6>; defn - Multiply by 2</dim>
```

**Type with related symbols** (drawer headers and name bodies are R6 dim):
```
<cyan R4>:user/Color</cyan> <dim R6>; deftype</dim>
<dim R6>; match:</dim>
<dim R6>;  Red Green Blue</dim>
```

**Error:**
```
<bold-red R8>Error:</bold-red> <red R9>Unbound symbol 'foo'</red>
```

**Slash command `/list`** (only the R12 category headers are styled; the name bodies are the layout family, default-styled, out of styling scope per §10.3):
```
<bold R12>Types:</bold>
  Color Point
<bold R12>Fns:</bold>
  double area
```

The reset between the R4 cyan type prefix and the value is the space character — no visible break, just a colour transition. The classification comment (everything from `; ` onward on the primary line) is a single R6 dim span. A string result value renders as one R3 green span; a constructor value (`Color.Red`) and a closure (`<closure>`) are R15 default.

### 10.5 Batch Mode Output [R4 S22]

Batch mode (`--run`) writes to stdout which is typically not a TTY. Per §10.1, ANSI sequences MUST be suppressed. The `:Type value` format is emitted as plain text. Error messages to stderr MUST also be plain text in batch mode (stderr TTY status is checked independently — if stderr is a TTY but stdout is not, errors MAY be styled on stderr).

### 10.6 Showcase Player Styling [R4 S22]

The showcase player (`repl/showcase`) MAY apply the same colour palette during replay. Specifically:

- Prompt lines SHOULD use dim styling, matching the REPL prompt.
- Simulated user input SHOULD use default (no styling) — matching the visual weight of real typing.
- Output lines SHOULD be styled using the same rules as §10.3 (cyan for types, dim for comments, red for errors).
- The `[paused]` indicator SHOULD use dim styling.
- The showcase player MUST respect `NO_COLOR` and TTY detection using the same logic as the REPL (§10.1), minus the `--no-color` flag (the player has its own invocation interface).

### 10.7 Implementation Notes [R4 S22]

The styling layer SHOULD be implemented as a small module (e.g., `src/style.rs`) that provides a `Style` enum and a `styled(text, style) -> String` function. When colour is disabled, `styled` returns the text unchanged. All REPL output code calls `styled` — there are no raw `\033[` literals scattered through the codebase.

The TTY detection result SHOULD be computed once at startup and stored as a boolean. Checking `isatty()` on every line would be wasteful and could produce inconsistent output if stdout is redirected mid-session (which is not a supported scenario but should not cause crashes).

**Ring 4 Sprint 22**: Full terminal styling specification. Implementation targeted for a subsequent sprint.

### 10.8 Interactive Line Editor and Input History [S106]

On an **interactive terminal**, the REPL MUST provide a line editor with **command history** and
**basic in-line editing** — the universal shell/REPL convention. Before S106 the read loop used a
plain buffered line iterator (`stdin.lock().lines()`), so the up-arrow did nothing and there was
no cursor editing (FIXME 0544). This section makes the line editor a normative requirement and
pins the TTY gate + non-TTY fallback that keeps scripted/piped input working unchanged.

**Implementation crate — `rustyline` (`/arch` Phase-2 §1 ruling, S106).** The line editor MUST be
backed by **`rustyline`**, adopted as a **default-build** dependency of the `cranelisp` binary
(not feature-gated) — it is markedly lighter than reedline's crossterm/nu stack and far smaller
than the agent feature's HTTP/async tree, and it already owns the §14.3
`ExternalPrinter` notification-reinstatement path. This is a binary-crate dependency only: no
crate-boundary surface, no `public-api.txt` change. [S106]

**History recall (MUST).** On an interactive TTY:

- **Up-arrow** recalls the **previous** input entry; **down-arrow** moves toward the **more
  recent** entry (and past the newest, back to the current fresh line). Repeated up/down cycles
  through the history in order. [S106]
- Each **successfully read input line** is added to the history. An implementation MAY skip
  adding an entry that is empty or identical to the immediately preceding entry (the standard
  "no consecutive duplicates" convention); this is at implementation discretion. [S106]
- History recall populates the edit buffer with the recalled text; the user MAY edit it before
  submitting, and MAY submit it unchanged. [S106]

**In-line editing (MUST, basic set).** On an interactive TTY the editor MUST support at minimum:
left/right cursor movement, insertion and deletion at the cursor (backspace/delete), and
beginning/end-of-line movement. Richer editing (word-wise movement/delete, kill/yank, reverse
history search) is **SHOULD** — rustyline provides the standard Emacs-style bindings by default,
and the REPL SHOULD leave them enabled. [S106]

**TTY gate + non-TTY fallback (MUST — BLOCKING invariant).** The line editor is constructed and
used **only** on the interactive branch, gated on `std::io::IsTerminal` for **stdin**. When stdin
is **not** a terminal — piped or redirected, which is how the e2e harness and scripted input drive
the REPL — the read path MUST remain the **exact** plain line-reading behaviour (`stdin` locked,
read line-by-line), and rustyline MUST NOT be instantiated. The non-TTY output MUST be
**byte-for-byte identical** to the pre-S106 behaviour: the line editor changes the *interactive*
experience only and MUST NOT alter a single byte of piped/redirected session output. This is both
a normative pin here and a `/qa` guard (assert non-TTY output byte-identical pre/post). [S106]

**Non-TTY invalid-UTF-8 carve-out — deliberate divergence (`/review`-sanctioned) [S106].** The
byte-identical guarantee above holds for **valid UTF-8** input. Because S106 rewrote the non-TTY
read path from `stdin.lock().lines()` to a direct byte-wise fd-0 reader, **invalid/malformed
UTF-8** now diverges from pre-S106 by design: the new reader applies **lossy substitution**
(U+FFFD) and the **session continues** — a malformed byte is NOT treated as end-of-input. Pre-S106,
`.lines()` returned an error on invalid UTF-8 which the read loop treated as EOF, **killing the
session**. This is a deliberate improvement judged BETTER by `/review` (a stray non-UTF-8 byte no
longer terminates the session) and MUST NOT be re-broken back to the session-terminating behaviour.
[S106]

**Single input source — the agent consent-line read goes through the SAME editor (MUST).** The
agent write-consent gate (§17.14, §15.2 write gate) reads the next input line to answer its
`[y/N]` prompt. On the interactive branch that read MUST go through the **same `rustyline` editor
instance** (a `readline` call), **not** a parallel `BufReader` alongside it: rustyline owns the
terminal (raw mode during a read, cooked between), so a second raw reader would desync the line
discipline and race the buffer. On the non-TTY branch the consent read stays the same plain
line read from the same single reader. The REPL threads **one** input abstraction with a TTY impl
(editor-backed) and a non-TTY impl (plain lines); the consent seam calls that abstraction, never a
second reader. [S106]

**Interaction with the §14.3 notification-reinstatement note.** §14.3 already names
rustyline's `ExternalPrinter` as the home for the "reinstate partial input after a notification"
behaviour. The line editor is the natural owner of that behaviour: once the editor is wired in, a
watcher/agent notification arriving mid-input SHOULD print on a new line and reinstate the partial
input via `ExternalPrinter` (still a SHOULD/nice-to-have per §14.3, not upgraded to a MUST here).
[S106]

**Testability note (coverage gap, honest).** Interactive arrow-key behaviour is observable **only
on a real TTY**, which the piped-stdin e2e harness cannot drive. The durable automated guard is
therefore the **non-TTY-byte-identical** assertion (above) plus any library-level history-recall
unit test the chosen crate supports; the TTY-interactive surface (arrow keys, cursor editing) is
**manually verified** in the `/repl` demo and flagged as an explicit e2e coverage gap — do not
claim e2e coverage of arrow keys. [S106]

**History persistence and bounded length (SETTLED [S106]).** These two user-experience decisions
(routed by `/arch` Phase-2 §1 to `/repl` → user, not architecture questions) are now ruled:

- **History persistence — per-project, to `<project_root>/.cranelisp_history` (MUST).** The command
  history persists across sessions in a history file at `<project_root>/.cranelisp_history`, where
  `project_root` is resolved per §0.5.1 — **not** the user's home directory. History is therefore
  **per-project**: each project carries its own REPL history file beside its sources, so recall
  reflects the work done in that project rather than a single global stream. The file is loaded at
  TTY-session start and appended on `/quit`, so a user's prior-session history survives a restart.
  rustyline supports this directly (`Editor::load_history` / `save_history`). The persistence file
  MUST degrade gracefully: an unreadable/unwritable history file is a non-fatal warning, never a
  failed session launch (same posture as the §0.5.7 scaffold). [S106]
- **Bounded history length — cap at 1000 entries (MUST).** History MUST be bounded so it does not
  grow without limit. The cap is **1000 entries** (rustyline's own default `max_history_size`),
  oldest entries dropped first (FIFO). [S106]
