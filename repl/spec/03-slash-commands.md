> [REPL specification index](index.md)

## 3. Slash Commands

Slash commands provide introspection and navigation. All commands start with `/` and are NOT expressions — they are REPL-only features.

### 3.1 Command Inventory

Per-row annotations below indicate test coverage for each command. Ring 4 introspection commands (`/disasm`, `/time`, `/mod`, `/reload`) are legitimately pending. (`/mem` E2E coverage landed Sprint 58 Wave 5.)

| Command | Aliases | Description | Ring | Test |
|---|---|---|---|---|
| `/help` | `/h` | Show available commands and usage | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/sig <name>` | `/s` | Show signature with typed parameters (§3.8) | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/doc <name>` | `/d` | Show docstring (including builtins — see spec/appendix-a-builtins.md §A.5) | 0 | [R1] |
| `/type <expr>` | `/t` | Show type without evaluating | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/info <name>` | `/i` | Full details: type, classification, code size, compile time | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/source <name>` | — | Show original source text | 0 | [R4 S10] |
| `/sexp <name>` | — | Show parsed S-expression | 0 | [R4 S10] |
| `/ast <name>` | — | Show AST | 0 | [R4 S10] |
| `/clif <name>` | — | Show Cranelift IR | 0 | [R4 S10] |
| `/disasm <name>` | — | Show disassembled native code | 0 | [R4 S10] |
| `/list [prefix]` | `/l` | List definitions in current module | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/time <expr>` | — | Evaluate with timing breakdown | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/expand <form>` | `/e` | Macro-expand a form | 3 | [R3 S16] |
| `/mod [name]` | — | Switch module namespace | 2 | [R4 S10] |
| `/imports [module]` | — | Show imports and special forms; filter by source module | 0 | [Tested+Neg tests/repl_introspection::imports_lists_special_forms, tests/repl_introspection::imports_neg_no_primitives_leak_on_fresh_session] |
| `/exports <module>` | — | List a module's importable public symbols | 2 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/mem [expr]` | `/m` | Show allocation statistics (see §3.7) | 4 | [Tested tests/repl_introspection::sig_shows_type_signature] |
| `/run-tests [module]` | `/rt` | Discover and run test functions (see §16) | 4 | [R4] |
| `/run-all-tests` | — | Run all tests in project (see §16) | 4 | [R4] |
| `/sh <cmd>` | — | Run a shell command (see §13) | 4 | [R4 S52] |
| `/refs <sym>` | — | List sites that reference a symbol (reverse query; LLM-free — see §17.6) | 4 | [S88] |
| `/tests-for <sym>` | — | List test functions that reference a symbol (reverse query; LLM-free — see §17.6) | 4 | [S88] |
| `/doc <module>` | `/d` | Read a module's preamble (module-level documentation — see §17.5); `/doc <name>` reads a definition docstring (§3.1, builtins) | 0 | [S88] |
| `/ask <text>` | — | The explicit agent door — routes `<text>` to the embedded agent **unconditionally**, bypassing the resolution-aware classifier (useful even for a *known* symbol's prose; see §17.1); prints "agent not built in" when the feature is off | 4 | [S88] |
| `/context <path>` | — | **Debug command** — write the agent's full **assembled** next-turn request (system primer, harvested context, tools, transcript, current turn) to `<path>` as readable text, **without calling the model** (works dormant/offline, no key; see §17.11); human-only, not an agent tool; prints "agent not built in" when the feature is off | 4 | [Tested+Neg tests/agent.rs::context_feature_off_prints_not_built_in, tests/agent.rs::agent_on_context_dumps_request_to_file_dormant] |
| `/syntax [topic]` | — | Core-language syntax cheat-sheet — bare `/syntax` lists topics, `/syntax <topic>` shows that topic's dense, verified-compiling content (see §17.17); a human REPL command **and** an agent pull-tool; LLM-free (a static curated asset, works with the agent absent) | 4 | [S90] |
| `/search <query>` | — | Search public non-macro symbols reachable on the lib search path ∪ the project root by name, scheme, or docstring (see §17.19). An exact in-scope name match remains visible as `already in scope — no import needed`; source indexing does not execute macro expansion. A **normal default-build session facility** (not agent-gated), also reached by the agent via the ordinary pull | 4 | [Tested+Neg tests/search::search_by_name_exact_returns_four_facets, tests/search::search_by_scheme_partial_contains, tests/search::search_neg_no_match_self_documenting_note] |
| `/quit` | `/q` | Exit REPL | 0 | [Tested tests/repl_introspection::sig_shows_type_signature] |

### 3.2 `/help` Output [Tested tests/repl_introspection::help_lists_commands]

`/help` MUST list all available commands with a brief description. The output MUST be organized by category:

```
Available commands:
  /help (/h)        Show this help
  /sig (/s) <name>  Show signature
  /doc (/d) <name>  Show docstring
  ...
```

Commands not yet available (due to ring) SHOULD be omitted or marked as unavailable.

### 3.3 `/list` — Module Definitions [Tested tests/repl_introspection::list_empty_session]

`/list` shows symbols **defined in the current module** — the user's own work. It does NOT show imports or special forms (those belong on `/imports`). Constructors are included alongside other symbols alphabetically.

**Scope rule:** `/list` MUST show only names created by definitions in the current module: `defn`, `deftype`, `deftrait`, `impl` (trait method definitions), `defmacro`. Imported names MUST NOT appear. [Tested+Neg tests/repl_introspection::list_empty_session] Special forms MUST NOT appear (they are always available and shown by `/imports`). [Tested+Neg tests/repl_introspection::list_neg_no_special_forms_category] Primitives (`add-i64`, etc.) MUST NOT appear when the current module is `user`. [Tested+Neg tests/repl_introspection::imports_neg_no_primitives_leak_on_fresh_session]

**Categories:**

| Category | Contents | Ring | Test |
|---|---|---|---|
| Modules | Declared submodules | 2 | [R4 S15] |
| Macros | Macro definitions (`defmacro`) | 3 | [Tested+Neg tests/repl_introspection::list_empty_session] |
| Traits | Trait declarations (`deftrait`) | 2 | [Tested tests/repl_introspection::list_empty_session] |
| Types | User-defined types and constructors (`deftype`) | 0 | [Tested+Neg tests/repl_introspection::list_empty_session] |
| Fns | User-defined functions, trait method implementations, and field accessors | 0 | [Tested tests/repl_introspection::list_empty_session] |

Category order: Modules, Macros, Traits, Types, Fns. Empty categories are omitted. [Tested+Neg tests/repl_introspection::list_empty_session]

**Field accessors — canonical qualified form (`Type.field`).** Each field of a `deftype` produces a field accessor. Under the field-accessor model (`spec/05-definitions.md §5.2.6`, `spec/08-modules.md §8.5.2`), the accessor's **canonical** name is the qualified `Type.field` form (e.g. `Box.v`): a real, Public definition that `/list` MUST display under **Fns**, using the qualified `Type.field` form — consistent with the REPL's qualified-display convention (`:primitives/Int`, `:(Fn [a] a) user/id`; the §"Design Principle" rule that names are always fully qualified to teach the module system). [S91 tests/spec_field_accessor.rs::list_shows_canonical_qualified_accessor]

The **bare** field name (e.g. `v`) is a **convenience alias** to the canonical accessor — it resolves when unambiguous and is an ambiguity error when two in-scope types share the field name. The bare alias is **NOT separately listed** by `/list` (option A — show canonical only): listing both `Box.v` and a bare `v` would double-count every field, and the bare alias is import-class (an alias into the current scope), so it falls under the existing "imported/alias names MUST NOT appear on `/list`" scope rule above. `/list` shows the canonical accessor exactly once, under its `Type.field` name. [S91 tests/spec_field_accessor.rs::list_shows_canonical_qualified_accessor]

**Constructors — canonical qualified `Type.Ctor` form, listed once (S109).** With the
dotted-`Type.Ctor` constructor capability (`sprints/SPRINT.md` bucket 2 — same-named constructors
coexisting across in-scope types, e.g. `Maybe.Some`/`Option.Some`), each constructor has a
**canonical** `Type.Ctor` key (`Maybe.Some`) and a **bare-name alias** (`Some`) — exactly the
inverted model of field accessors above. `/list` MUST therefore treat constructors the **same way**
it treats field accessors (mirroring FIXME 0438 and the E4 seam): the canonical `Type.Ctor` entry is
the real definition and is listed **once** under its qualified `Type.Ctor` name in the **Types**
category; the bare ctor name (`Some`) is a **convenience alias** (import-class, an ambiguity error
when two in-scope types share it) and is **NOT separately listed**. `/list` MUST NOT double-list a
constructor as both `Maybe.Some` **and** a separate bare `Some` — that would double-count every
constructor exactly as bare+canonical field accessors would. A constructor appears in `/list`
exactly once, under its `Type.Ctor` name. (The per-type `; match:` related-symbol drawer of a bare
**type** lookup, §1.1, is a different surface — it lists that one type's own constructors and is
unambiguous within the type; this rule governs the flat category listing where cross-type
same-named ctors would otherwise collide.) [Tested tests/repl_introspection::list_types_includes_constructor_rows_under_canonical_dotted_form, tests/repl_introspection::list_shows_ctor_once_canonical]

**Empty module:** When no definitions exist in the current module, `/list` MUST print `(no definitions)`. [Tested tests/repl_introspection::list_empty_session] This distinguishes "command worked on empty module" from a failed command.

**Negative requirements** (what MUST NOT appear): [Tested+Neg]

- No category should contain imported names (those belong on `/imports`) [Tested+Neg tests/repl_introspection::list_empty_session]
- No category should contain special forms (those belong on `/imports`) [Tested+Neg tests/repl_introspection::list_empty_session]
- No category should contain compiler-internal symbols (`__macro_*`, `$`-mangled names) [R4 S15]
- Constructors MUST appear in Types, not in Fns [Tested+Neg tests/repl_introspection::list_empty_session]
- A field accessor MUST appear only once, under its canonical `Type.field` name; the bare-field alias (`v`) MUST NOT appear as a second, separate accessor entry [S91 tests/spec_field_accessor.rs::list_shows_canonical_qualified_accessor]
- A constructor MUST appear only once, under its canonical `Type.Ctor` name; the bare-ctor alias (`Some` for `Maybe.Some`) MUST NOT appear as a second, separate constructor entry [Tested tests/repl_introspection::list_shows_ctor_once_canonical]

**Filter argument:** `/list <text>` performs a case-insensitive prefix match on symbol names across all categories, showing matching symbols with full type info. [Tested tests/repl_introspection::list_prefix_filter_matches_names] `/list` with no argument shows all definitions. [Tested tests/repl_introspection::list_empty_session]

**Large category display layout algorithm** [Tested+Neg repl/spec.md→tests/repl_introspection.rs::layout_cross_command_list_exports_byte_identical]**.** The multi-column line-breaking layout below is a **normative MUST**, not advisory. It is a deterministic, exactly-reproducible contract — the same input symbol set MUST always produce byte-for-byte identical output. Because this layout is **shared verbatim** by `/list` (§3.3), `/imports` (§3.4), `/exports` (§3.5), and related-symbol lists (`04-self-documentation.md` §4), divergence between any two of those commands is a conformance defect, not a stylistic variation. Each rule below is individually checkable.

The layout is a **MUST** (not SHOULD) so that exact output can be asserted in tests and so the four commands stay mutually consistent. Each numbered rule is a separate conformance obligation:

- **L0 — Single-line threshold (the <7 case).** A category with **fewer than 7 names** MUST be rendered on a single line after the category label, space-separated, with no line-breaking applied. The breaking rules L1–L4 MUST NOT be applied below the 7-name threshold. [Tested+Neg repl/spec.md→tests/repl_introspection.rs::list_layout_l0_under_seven_single_line, tests/repl_introspection.rs::list_layout_l0_neg_exactly_six_not_broken]

- **L1 — 7-or-more triggers breaking.** A category with **7 or more names** MUST apply the line-breaking layout (rules L2–L4). The threshold is exactly 7: 6 names stay on one line (L0), 7 names break. [Tested repl/spec.md→tests/repl_introspection.rs::list_layout_l1_seven_triggers_break]

- **L2 — Operators first, on their own break.** Non-alphabetic symbols (operators such as `+`, `-`, `*`, `!=`, `<=`) MUST be displayed before all alphabetic names, wrapping at 6 per line. After the last operator, a new line MUST start: an operator MUST NEVER share a line with an alphabetic name. [Tested+Neg repl/spec.md→tests/repl_introspection.rs::list_layout_l2_operators_first_own_line, tests/repl_introspection.rs::list_layout_l2_neg_operator_never_shares_name_row]

- **L3 — Letter groups never split; early-break to stay together.** Alphabetic names MUST be grouped by first letter (case-insensitive) and the groups emitted in sorted order. Before appending a letter group to the current row, if `current_count + group_size > 6` the current row MUST be flushed first. A letter group MUST therefore appear either entirely on the current row (alongside earlier groups) or starting on a fresh row — it MUST NEVER be split across a row boundary, **except** when the group alone has 7+ names (then L4 applies). [Tested+Neg repl/spec.md→tests/repl_introspection.rs::list_layout_l3_letter_group_early_break, tests/repl_introspection.rs::list_layout_l3_neg_no_group_straddles_row]

- **L4 — Hard wrap at 6 within an oversized group.** A single letter group with **more than 6 names** MUST wrap at 6 names per line within itself. [Tested repl/spec.md→tests/repl_introspection.rs::list_layout_l4_oversized_group_wraps_at_six]

The example below is illustrative of the rules above; it is the reference layout that tests assert as expected output.

> **L3 rule-vs-example reconciliation (SETTLED [S106], FIXME 0545).** The pre-S106 illustrative
> example **contradicted the L3 rule text**: it placed `double drop` (the `d` group, size 2) on a
> fresh row even though the preceding row held only `abs add ceil concat` (4 names), and
> `4 + 2 = 6 ≤ 6`, so L3-as-worded requires appending the group to that row. The same
> eager-new-line-per-letter divergence recurred at the `e`/`f` groups, and the operator line showed
> 9 operators unwrapped despite L2's "wrapping at 6 per line". So the RULE and the EXAMPLE genuinely
> disagreed. **Ruling: the L0–L4 rule is the intended truth; the old example was flawed.** This
> matches the user's stated intent (FIXME 0545): *"up to six per line … UNLESS the current line has
> fewer than six symbols AND the next letter's group completes within the remaining gap to six (then
> keep it on the same line)"* — which is **exactly** the L3 pack-to-six rule, not the eager
> per-letter behaviour the old example encoded. The flawed example is replaced by the corrected,
> fully L0–L4-conformant reference layout below (operators wrapped at 6 per L2; alphabetic groups
> packed to six per L3). [S106]

Reference layout (matches L0–L4 exactly for this name set: operators
`+ - * / < > <= >= !=`; then groups a=`abs add`, c=`ceil concat`, d=`double drop`,
e=`empty? even?`, f=`filter floor fold`, g=`get`):

```
Fns:
  + - * / < >
  <= >= !=
  abs add ceil concat double drop
  empty? even? filter floor fold get
```

Row-by-row derivation (for the tests to pin): operators (9) wrap at 6 → `+ - * / < >` then
`<= >= !=`, then a mandatory break (L2). Alphabetic packing (L3): a(2)→count 2; c(2)→4; d(2)→6
(row full: `abs add ceil concat double drop`); e(2) would make 8>6 → flush, new row count 2;
f(3)→5; g(1)→6 (`empty? even? filter floor fold get`). [S106]

### 3.4 `/imports` — Imports and Special Forms [Tested+Neg tests/repl_introspection::imports_lists_special_forms]

`/imports` shows everything available in the current module that was NOT defined here: imported names and language special forms. This is the complement of `/list` — together they cover all symbols in scope.

**Categories:**

| Category | Contents | Ring | Test |
|---|---|---|---|
| Special forms | `if`, `let`, `fn`, `defn`, `deftype`, `match`, etc. | 0 | [Tested tests/repl_introspection::imports_lists_special_forms] |
| Macros | Imported macro definitions | 3 | [R4 S15] |
| Traits | Imported trait declarations | 2 | [R4 S15] |
| Types | Imported types and constructors | 0 | [R4 S15] |
| Fns | Imported functions and trait methods | 0 | [Tested tests/repl_introspection::imports_lists_special_forms] |

Category order: Special forms, Macros, Traits, Types, Fns. Empty categories are omitted (except Special forms, which are always present). [Tested tests/repl_introspection::imports_lists_special_forms]

**Format:** Each category lists names using the **same normative layout algorithm** as `/list` (§3.3 rules L0–L4) — names only, no type signatures. The layout MUST be byte-for-byte identical to what `/list` produces for the same name set (one shared formatter, not a re-implementation). Type the symbol name for more detail. [Tested+Neg repl/spec.md→tests/repl_introspection.rs::layout_cross_command_list_exports_byte_identical, tests/repl_introspection.rs::list_layout_neg_names_only_no_type_sigs]

**Source module filter:** `/imports <module-name>` filters to show only imports from that source module (exact match). [Tested tests/repl_introspection::imports_lists_special_forms] Names are grouped under `From <module>:` and sorted alphabetically. Source modules sorted alphabetically.

```
user> /imports prelude
From prelude:
  + - * / < > <= >= != =
  case cond
  show str
  ...
```

**Unfiltered mode:** `/imports` with no argument shows all imports organized by category (not by source module). [Tested tests/repl_introspection::imports_lists_special_forms] This gives a quick overview of what's available. Use `/imports <module>` for per-module detail.

**Re-export provenance:** When the user writes `(import [prelude [*]])` and the prelude re-exports `+` from `num.num`, `/imports prelude` shows `+` under `From prelude:` — because that is the module the user imported from. The ultimate origin is available via `/info +` (§3.6).

**Reexport entries:** Both `Import` and `Reexport` module entries MUST be included. [Tested tests/repl_introspection::imports_lists_special_forms] A symbol re-exported through the prelude is still an import from the user's perspective.

**Glob imports:** When `(import [mod [*]])` was used, `/imports` MUST show the individual names that were imported (the expansion of `*` at the time the import was evaluated), not just `*`.

**Implicit prelude import (Ring 3+):** The compiler injects an implicit `(import [prelude [*]])` for all non-prelude modules (spec §8.8.1). This implicit import IS visible in `/imports` — the user needs to discover what the prelude provides.

**No imports:** In a fresh session with no explicit `(import ...)` and no prelude, `/imports` MUST show only Special forms. [Tested+Neg tests/repl_introspection::imports_lists_special_forms, tests/repl_introspection::imports_neg_no_primitives_leak_on_fresh_session] The `primitives` module's implicit availability is via the module resolution fallback, NOT via import — so primitives do not appear in `/imports` unless explicitly imported.

**Error cases:**
- `/imports nonexistent` — no imports from that module; silent re-prompt (not an error) [Tested+Neg tests/repl_introspection::imports_lists_special_forms]

### 3.5 `/exports <module>` — Module Public API [Tested tests/repl_introspection::exports_no_arg_shows_usage]

`/exports <module>` resolves a module and lists its importable (public) symbols. This answers "what can I import from this module?" before writing an `(import ...)` form.

**Argument:** The module name is required. `/exports` with no argument MUST print a usage hint: `Usage: /exports <module-name>`. [Tested tests/repl_introspection::exports_no_arg_shows_usage]

**Module resolution:** The argument is resolved using the same resolution logic as `(import [module [...]])` — submodule paths, root modules, and stdlib modules. If the module is not yet loaded, it SHOULD be resolved and loaded (same as an import would trigger). If the module cannot be found, print an error: `Module '<name>' not found`. [Tested tests/repl_introspection::exports_no_arg_shows_usage]

**Output format:** Public symbols listed by category — names only, no type signatures. [Tested tests/repl_introspection::exports_no_arg_shows_usage] Categories use the **same normative layout algorithm** as `/list` (§3.3 rules L0–L4); the layout MUST be byte-for-byte identical to `/list` for the same name set. [Tested+Neg repl/spec.md→tests/repl_introspection.rs::layout_cross_command_list_exports_byte_identical, tests/repl_introspection.rs::list_layout_neg_names_only_no_type_sigs] Type the symbol name for more detail.

```
user> /exports math
Module 'math':
Fns:
  bar foo
```

Categories follow the same order as `/list`: Modules, Macros, Traits, Types, Fns. Names sorted alphabetically within categories.

**What counts as public:** Definitions with public visibility — `Def`, `Constructor`, `TraitDecl`, `TypeDef`, `Macro`. Import and Reexport entries in the target module are NOT shown (those are the module's own imports, not its exports).

**Field accessors in `/exports`.** A module's field accessors are public definitions and MUST be listed by `/exports` under their **canonical qualified `Type.field`** form (e.g. `Box.v`) — the same canonical/alias rule as `/list` (§3.3, "Field accessors — canonical qualified form"): the canonical accessor is the real Public `Def` shown by `/exports`; the bare-field name (`v`) is a convenience alias (import-class) and is NOT separately listed (option A — show canonical only), consistent with the "Import and Reexport entries are NOT shown" rule above. A field accessor appears in a module's exports exactly once, under its `Type.field` name. [S91 tests/spec_field_accessor.rs::list_shows_canonical_qualified_accessor]

**Constructors in `/exports`.** A module's constructors follow the **same canonical/alias rule**
(S109; mirroring the field-accessor rule above and §3.3's "Constructors — canonical qualified
`Type.Ctor` form"): with the dotted-`Type.Ctor` capability (bucket 2), the canonical `Type.Ctor`
entry (`Maybe.Some`) is the real Public definition `/exports` lists, **once**, under its qualified
`Type.Ctor` name; the bare-ctor alias (`Some`) is a convenience alias (import-class) and is **NOT**
separately listed. A constructor appears in a module's exports exactly once, under its `Type.Ctor`
name — never double-listed as both `Maybe.Some` and a separate bare `Some`. [S109 — `/testing` twin
owed]

**Empty module:** If the module has no public symbols, print `Module '<name>' has no public symbols`. [R4 S15]

**Filter argument:** `/exports <module> <prefix>` performs a case-insensitive prefix match within the module's exports. [R4 S15]

### 3.6 `/info` Output [Tested tests/repl_introspection::info_resolves_trace_special_form]

`/info <name>` MUST display multi-line details using the `:Type name` format:

```
:(Fn [primitives/Int] primitives/Int) user/double
  (defn double [x] (* x 2))
  48 bytes, 2ms
```

For overloaded functions, all variants MUST be listed. For constrained functions, specializations MUST be shown.

### 3.7 `/mem` — Allocation Statistics [Tested]

`/mem` reports the runtime allocation counters maintained by `cranelisp-runtime`: total allocations observed, total deallocations, and bytes currently live. The command has two shapes — a **snapshot** (no argument) and a **delta** (with an expression argument). Both are comment lines (`;`-prefixed), consistent with the self-documentation convention in §1.5.

**Snapshot — `/mem`** — MUST emit two comment lines:

```
user> /mem
; live: <bytes> bytes (<live-allocs> allocations)
; allocs: <total-allocs>  deallocs: <total-deallocs>
```

- `<bytes>` is `cranelisp_runtime::bytes_current()` — sum of currently-live heap allocations in bytes.
- `<live-allocs>` is `allocs - deallocs` — the number of allocations that have not been freed.
- `<total-allocs>` and `<total-deallocs>` are the cumulative counters since process start.

The two fields between `allocs:` and `deallocs:` are separated by two spaces. The `(<live-allocs> allocations)` group is singular or plural depending on count (the implementation MAY always use `allocations` for simplicity).

**Delta — `/mem <expr>`** — MUST evaluate the expression, display its result per §1.2 (for an IO expression, after the §1.2.1 notice and the action's platform output), then emit one comment delta line:

```
user> /mem (list 1 2 3)
:(collections.list/List primitives/Int) (List.Cons 1 (List.Cons 2 (List.Cons 3 List.Nil)))
; delta: allocs +<d-allocs>  deallocs +<d-deallocs>  bytes <±d-bytes>  live <±d-live>
```

- `<d-allocs>`, `<d-deallocs>` are non-negative deltas (prefixed `+`).
- `<d-bytes>` and `<d-live>` are signed deltas (`+`/`-`) because rebinding `it` can release previously-live allocations, making the delta negative.
- Each field is separated from the next by two spaces.

Evaluation errors MUST still emit the delta line — observation is the point, and a failed allocation is itself interesting data. The header line in the error case uses the standard §5 error format.

**The delta window MUST include the program-result release.** [S119 — FIXME 0914] The purpose of `/mem <expr>` is to let a user at the prompt answer "did my expression's memory get reclaimed?", so the window the delta measures MUST be closed *after* the turn's result has been released, not after evaluation. A window that closes earlier reports `live +N` for every heap-valued expression — including expressions whose result the runtime provably reclaims — which tells the user they have a leak when they do not. This is a **truthfulness** requirement on the instrument, not a precision one: a diagnostic that systematically over-reports growth is worse than no diagnostic, because a user debugging their own ownership will act on it.

Because the REPL renders a turn's whole `StyledDoc` before releasing that turn's result (`src/CLAUDE.md` §"Program-result ownership" — observe, then release), the delta line is *part of the text emitted before the release*, so satisfying this requirement is an ordering question, not a counter question. Two shapes satisfy it; the choice is the implementation's:

- the command takes responsibility for its own turn's release, releasing before it computes the closing counters; or
- the delta line is emitted after the release rather than composed with the result line.

Until this holds, the **snapshot** form is the truthful instrument and the delta form's exclusion MUST be treated as a known non-conformance rather than as the specified behaviour.

`/mem` MUST NOT start the runtime; the counters are valid from process start. An empty runtime reports `; live: 0 bytes (0 allocations)` and `; allocs: 0  deallocs: 0`.

| Requirement | Test |
|---|---|
| snapshot emits live + totals | [Tested tests/repl_introspection::mem_snapshot_emits_live_and_allocs_neg_no_delta] |
| delta prints result then delta line | [Tested tests/repl_introspection::mem_with_expr_emits_signed_delta_line, tests/repl_introspection::mem_with_io_expr_prints_notice_then_payload_then_delta] |
| signed `bytes` and `live` deltas | [Tested tests/repl_introspection::mem_snapshot_emits_live_and_allocs_neg_no_delta] |
| baseline counters at process start are zero | [Tested tests/repl_introspection::mem_snapshot_emits_live_and_allocs_neg_no_delta] |
| `/m` short alias produces snapshot | [Tested tests/repl_introspection::mem_snapshot_emits_live_and_allocs_neg_no_delta] |

### 3.8 `/sig` Output — Same Primary Line as Bare Lookup [S102]

`/sig <name>` shows the symbol's signature. Its output is not a separate format: the
primary line(s) `/sig` prints MUST be **byte-identical** to the primary line(s) a bare
lookup of the same name prints (§1.1 universal format, §4.1 per-class rules) —
fully-qualified type per §1.4, fully-qualified symbol name, and the same
`; {classification} - {docstring}` drawer. For overloaded functions and macros, `/sig`
prints the same per-variant / per-clause signature lines as bare lookup (§4.1.1, §11.2.3).
For a spelling with several candidates, `/sig` prints the same per-candidate lines as bare
lookup — every candidate, never an ambiguity error (§4.1.11).
```
user> /sig double
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2
```

Unqualified type names or an unqualified symbol name in `/sig` output are non-conformances
([root CLAUDE.md, Design Principles](../../CLAUDE.md#design-principles) — `:Type value` notation with fully-qualified names):
`:(Fn [Int] Int) double ; defn` is wrong in both positions. [S102]

> Arbitration record (FIXME 0492, S102): the short-form rendering the binary produces today
> was ruled an implementation defect, not a spec defect — every governing display rule
> (§1.1, §1.4, §4.1, §11.2.3, §17.18.1) already mandated the fully-qualified form;
> this section makes the `/sig`-specific consequence explicit. Fix owner: `/int`
> (`repl.rs` `handle_sig` display seam).

| Requirement | Test |
|---|---|
| `/sig` primary line is byte-identical to bare lookup's (FQ type + FQ name + drawer) | [Uncovered S121 — the prior guard used the retired broken-symbol state] |

### 3.9 `/mod` — Namespace Switch and Turn-Environment Parity [S102]

`/mod [name]` switches the active module namespace. Its interactive behaviour — the prompt
changes to the new module, no confirmation is printed, bare `/mod` returns to the entry
module (§0.5) [Tested tests/repl_lifecycle.rs::mod_no_arg_returns_to_entry_module_not_user, tests/repl_lifecycle.rs::mod_no_arg_default_entry_is_user], an
unknown module gives an actionable error — is specified by the §8 module scenarios; this
section pins the **compilation-environment** contract, which is the load-bearing invariant for
the file-backed dev loop (`/mod M` + a defining form, editing a module in place).

**Turn-environment parity (MUST).** A form entered in a module-namespace turn (`/mod M`
followed by a `defn`/`deftype`/expression) MUST compile in the **same environment the module
`M`'s file body was compiled in**. Concretely, all of the following MUST be in scope for that
turn exactly as they are when `M`'s `.cl` file is loaded:

- the **implicit prelude values** — the prelude-provided operators and functions (`+`, `-`,
  `show`, …) are available as bare names (spec `08-modules.md` §8.8.1's implicit
  `(import [prelude [*]])`); [S102]
- the **prelude type aliases** — a bare `:Int` annotation resolves to `:primitives/Int` in the
  turn's forms exactly as in the file body (spec `08-modules.md` §8.9.1); [S102]
- **`M`'s own imports** — every name `M`'s file imports is in scope under the same binding it
  has in the file body. [S102]

**Parity is install-path-independent (MUST).** The environment MUST match `M`'s file-body
environment **regardless of how `M` was installed this session** — whether `M` was freshly
typechecked, or **restored from the module cache**. A cache-restored module MUST NOT present a
degraded namespace turn (e.g. a restored module whose session environment lacks the prelude, so
`(+ x 1)` fails with `undefined variable: +`). This is the parity axis: fresh and
cache-restored `/mod M` turns are indistinguishable to the user. [S102]

| Requirement | Test |
|---|---|
| a `/mod M` turn using prelude operators compiles (fresh session) | [Tested tests/repl_mod_devloop.rs::devloop_fresh_prelude_using_mod_turn_compiles] |
| the SAME turn compiles identically in a cache-restored session (parity axis) | [Tested tests/repl_mod_devloop.rs::devloop_cache_restored_prelude_using_mod_turn_compiles] |
| a bare `:Int` type alias resolves in a `/mod M` defining turn | [Tested tests/repl_mod_devloop.rs::devloop_fresh_mod_turn_bare_type_alias_resolves] |

### 3.10 Module-Qualified Arguments to Introspection Commands [S102]

The introspection commands' argument grammar MUST accept a **module-qualified name**
(`module/symbol`, spec `08-modules.md` §8.5.1) wherever they accept a bare symbol name. This is
a self-documentation requirement, not a convenience: the REPL's **own reports print
module-qualified names** — `/list`, `/imports`, and `/refs` all render definitions and
references as `m/mf` — and a name the REPL prints MUST be pasteable back
into the command that reads it. A qualified name that the REPL emits but its own introspection
commands reject is a broken self-documentation loop.

- **`/sig`, `/info`, `/doc`, `/source`, `/refs`, `/tests-for` MUST resolve a module-qualified
  argument** to the same symbol the bare form resolves to (when in scope), producing the same
  output. `/sig m/mf` MUST NOT report `unknown symbol 'm/mf'` while bare `mf` is imported and
  `m` is loaded. [S102]
- **`/sig` (and `/info`) on an imported bare name MUST print the full §3.8 primary line** — the
  `:(Fn …) m/mf ; defn - {doc}` signature line — not merely a `; imported from m/mf`
  provenance note with no signature. An imported name is as introspectable as a locally-defined
  one. [S102]
| Requirement | Test |
|---|---|
| `/sig` accepts a module-qualified name | [Tested tests/repl_mod_devloop.rs::sig_accepts_fq_module_qualified_name] |
| `/info` accepts a module-qualified name | [Tested tests/repl_mod_devloop.rs::info_accepts_fq_module_qualified_name] |
| `/refs` accepts a module-qualified name (bare form is the control) | [Tested tests/repl_mod_devloop.rs::refs_accepts_fq_module_qualified_name, tests/repl_mod_devloop.rs::refs_bare_name_lists_cross_module_caller_control] |
| `/sig` on an imported bare name prints the full §3.8 primary line | [Tested tests/repl_mod_devloop.rs::sig_imported_name_shows_full_signature_line] |

### 3.11 Code Pretty-Printing — Aligned `let`/`match` Column Layout [S107]

`/sexp <name>` and `/source <name>` render a definition's parsed form through the shared
S-expression pretty-printer (the same printer §17.13.2 routes agent ```lisp fences through).
This subsection makes the layout of a **pair-structured binding vector** — the `let` binding
list and the `match` arm list — a **normative, byte-reproducible MUST**, so `/qa` can assert the
exact output for a fixed fixture. It resolves FIXME 0554 (the pre-S107 printer was pair-unaware
and smeared binding pairs across lines). Everything below is a display contract only — it changes
no language semantics and no other form's layout.

**Structural recognition (Phase-2 durability constraint — binding on `/dev(src)`).** Pair-awareness
MUST be implemented as **structural recognition on the `Sexp` tree**, not string post-processing:
the printer recognises the binding/arm `Sexp::Bracket` of a recognised head as a sequence of
`(left, right)` pairs and lays it out from the tree. The recognised heads for S107 are exactly
**`let`** (the binding vector is its first `[...]` argument) and **`match`** (the arm vector is the
`[...]` argument following the scrutinee). Other binding-vector special forms MAY adopt the same
layout later; `let` and `match` are the required set this sprint.

**A "pair-structured vector"** is the recognised `[...]` argument read as consecutive pairs:
`[l0 r0 l1 r1 …]` → pairs `(l0,r0) (l1,r1) …`. The **left term** is the binding name (`let`) or the
pattern (`match`); the **right term** is the value (`let`) or the arm body (`match`).

**Layout rules (each an individually checkable MUST):**

- **P0 — Trigger.** A pair-structured vector with **2 or more pairs** MUST render in aligned
  pair layout (P1–P4). This **forces the enclosing `let`/`match` form multi-line even when it would
  otherwise fit the flat threshold** — an aligned two-arm `match` never collapses to one line. A
  vector with **0 or 1 pair** has nothing to align and follows the pre-existing flat/threshold
  layout unchanged. [S107]
- **P1 — One pair per line.** In pair layout each `(left, right)` pair MUST begin on its own line.
  A pair's left term, the next pair's left term, and any right term MUST NOT share a line
  (the pre-S107 smear defect). [S107]
- **P2 — Left column.** The left terms MUST be left-aligned into a single column whose start is the
  column immediately after the vector's opening `[`. Each left term is rendered flat. [S107]
- **P3 — Right column (deterministic alignment position).** Let `W` = the maximum flat width, in
  columns, over **all** left terms of that one vector. The right column start MUST be
  `leftColumnStart + W + 1` (one space of minimum separation after the widest left term). Every
  pair's right term MUST begin at that column; a left term narrower than `W` is padded with spaces
  to reach it. `W` is computed per vector (not globally), giving a single byte-reproducible
  alignment position. [S107]
- **P4 — Multi-line right terms indent under the right column.** When a right term is itself
  rendered multi-line (a nested `match`/`if`/`let`, or any form exceeding the flat threshold), its
  **first** line begins at the right column (P3) and **every continuation line** MUST be indented
  relative to the right-column start using the pretty-printer's ordinary recursive rules for that
  form (i.e. the nested form is printed as if its opening column were the right-column start). A
  nested pair-structured vector recursively obeys P0–P4 with its own per-vector `W`. [S107]
- **P5 — Graceful fallback.** A recognised vector with an **odd** element count (not cleanly
  pairable — malformed source) MUST fall back to the pre-existing non-pair bracket layout and MUST
  NOT crash or drop elements. [S107]

**Determinism.** For a fixed input `Sexp`, P0–P5 produce **byte-for-byte identical** output every
time (colour-off); with colour on, only SGR spans are added around the same characters, at the same
columns, per the **§10.3 token/element styling contract** (code roles R1 Head, R2/R3 literals, R4
type annotations, R5 source comments). This is the contract `/qa` pins against a fixed `let`/`match`
fixture. [S107]

**Worked example (byte-exact — the FIXME 0554 `rotate` fixture).** Source:

```
(defn rotate [p r] (let [d (match r [(L l) (- 0 l) (R r) r]) new-pos (+ (pos p) d) final-pos (if (< new-pos 0) (+ new-pos 100) new-pos)] (Position final-pos)))
```

`/sexp rotate` (and `/source rotate`) MUST render exactly (colour-off; the `defn`/params/`if`
wrapping is the pre-existing special-form body-indent layout, unchanged — only the aligned `let`
and nested `match` blocks are the S107 contract):

```
(defn rotate
  [p r]
  (let [d         (match r [(L l) (- 0 l)
                            (R r) r])
        new-pos   (+ (pos p) d)
        final-pos (if (< new-pos 0)
                    (+ new-pos 100)
                    new-pos)]
    (Position final-pos)))
```

Column derivation (for the tests to pin). The `let` sits at column 2 (the `defn` body indent), so
its `[` is at column 7 and the left column starts at column 8. The three left terms are `d` (width
1), `new-pos` (7), `final-pos` (9) → `W = 9`, so the right column starts at `8 + 9 + 1 = 18`: `d` is
padded with 9 spaces, `new-pos` with 3, `final-pos` with 1, and each value begins at column 18. The
`d` value is a two-arm `match` (P0 fires): its arm vector opens at column 27, its left column starts
at column 28, its two patterns `(L l)`/`(R r)` are each width 5 → arm right column `28 + 5 + 1 = 34`,
and the second arm continuation `(R r) r])` is indented to column 28 (P4). The `final-pos` value is a
multi-line `if` whose body lines indent to column 20 (`if` opens at column 18; ordinary +2 body
indent — P4 delegating to the existing rule). The binding vector's closing `]` attaches to the last
body line (`new-pos)]`). [S107]
