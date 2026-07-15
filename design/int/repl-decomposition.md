# `repl.rs` decomposition — S110 hygiene (FIXME 0606, R-1) — CUT SIGN-OFF

Owner: `/design` (int). Subordinate to `int.md` §3.3 (the session/REPL module map).
Authored Sprint 110 Phase 3. This is the **cut sign-off** the 0606 sequencing requires
(the 0580 `program.rs` template: `/design` signs off the module boundaries FIRST; `/dev`
performs the mechanical move LAST, behaviour-invariant, `public-api.txt` zero-diff). The
boundaries below are named precisely enough (function → target file, with current
`src/repl.rs` line ranges) that the Phase-5 move is mechanical.

`src/repl.rs` today: 5,234 lines — production runs to ~`:3885`; `:3886–5234` is
`#[cfg(test)] mod …`. ~185 production functions in one flat module mixing six
responsibilities. Target: four files, each carrying one responsibility, none over ~1,500
lines (production + its travelling tests).

## 0. The load-bearing fact that de-risks the move

**Every function in `repl.rs` is either an `impl CompilerSession` method or a module-free
`fn`, and `mod repl` is `pub(crate)` (a binary-crate internal module — no `public-api.txt`
boundary at all).** Consequences, exactly as the 0580 `program.rs` cut:

1. Because the split targets stay `impl CompilerSession` blocks in sibling files
   (`src/CLAUDE.md` §Session/REPL module map already declares `repl.rs` decomposed this
   way), **every `self.method()` call is unaffected by which file the method lives in** —
   the move re-homes definitions, not call sites. The only mechanical care is **visibility**
   of the shared free functions and the cross-file methods (`pub(crate)` where a sibling or
   `eval.rs`/`main.rs` calls it; `pub(super)` where only a `repl/` sibling does; **never
   `pub`**).
2. The binary has **no `public-api.txt`** (BC §6; Phase-2 Revision 3). The "pure
   decomposition" gate is therefore (a) **zero movement on any library crate's baseline**
   (none is touched — this is `src/`-only) and (b) e2e byte-identity (the golden REPL suite)
   + unit tier green. Do **not** invent a binary baseline to satisfy the letter of the claim.

**Framing for `/dev`: this is a file-organisation refactor, not an API refactor.** The real
risks are only (a) accidental visibility-widening and (b) mis-apportioning the shared
resolution/referer toolbox (§1.5) so a sibling can't reach it. There are **no phase-numbered
god functions to untangle first** (unlike 0580's `finalize_check_result_inner`) — the
largest single function is `dispatch_command` (`:512`, 167 lines) and it stays put in
residual `repl.rs`. So there is no in-place-split Stage A; the move is one stage.

## 1. The four target files (validated against the source function map)

Line numbers are current `src/repl.rs`. "prod ≈" is production lines only (tests split
separately, §2).

### 1.1 `repl/search.rs` — the `/search` UI subsystem (prod ≈ 460)

The interactive search UI half of `session_v4/index_worker.rs` (it belongs beside its
backend, `index-worker-isolation.md`).

| Item | `:line` |
|---|---|
| `handle_search` | `:1166` (146) |
| `indexing_note_text` `:1141`, `empty_result_message` `:1152`, `docstring_excerpt` `:64` | |
| `collect_name_and_docstring_hits` `:1312`, `exact_in_scope_hit` `:1334` | |
| `render_search_row` `:1359`, `render_search_row_doc` `:1372` | |
| `wait_for_index_settled` `:1425`, `try_search_by_scheme` `:1438` | |
| `is_already_in_scope` `:1470`, `symbol_is_bound` `:1493`, `scan_referers` `:1518` | |
| Items: `struct SearchRow` `:42`, `const SEARCH_INDEX_SETTLE_TIMEOUT` `:35`, `const SEARCH_INDEX_SETTLE_POLL` `:38`, `const DOC_EXCERPT_WINDOW` `:49` | |

### 1.2 `repl/format.rs` — the introspection-display `_doc` producer family (prod ≈ 1,050)

The `_doc` producers + `format_*` free functions + the `StyledDoc` span helpers — the
coherent sibling of `src/display.rs`. This is the **tight** file; see §2 for its test
apportionment and §1.5 for the layout-render pressure valve.

| Item | `:line` |
|---|---|
| Span helpers: `push_type_annotation` `:305`, `push_fq_name` `:310`, `push_metadata` `:316`, `push_warning_line` `:324`, `code_block_doc` `:332`, `classification_metadata` `:341` | |
| `describe_symbol` `:396` (55), `collect_related` `:451`, `collect_related_for` `:3178` | |
| Eval-result: `format_eval_result` `:2602`, `format_eval_result_doc` `:2618`, `format_eval_result_body_doc` `:2634` (115) | |
| Def entry: `format_def_entry` `:2749`, `format_def_entry_doc` `:2761` (157), `resolve_entry_for_display` `:2918` | |
| Type/trait/builtin: `format_type_display*` `:2955/:2963`, `format_trait_display*` `:3022/:3035`, `format_builtin_type_display*` `:3078/:3083`, `impls_for_type_in_view` `:3127`, `prelude_trait_head_is_public` `:3162` | |
| Special-form/macro: `format_special_form_display*` `:3254/:3262`, `format_macro_display*` `:3282/:3291`, `format_macro_clause_params` `:3317` | |
| Overloaded: `format_overloaded_variants*` `:353/:362` | |
| Related sections: `format_related_section_doc` `:3342`, `format_trait_related_sections*` `:3517/:3529`, `indent_source_block` `:3547`, `format_sexp` `:3808`, `append_docstring_comment` `:3837`, `format_mem_snapshot` `:286` | |
| Layout-render subfamily (pressure valve, §1.5): `format_symbol_layout` `:3693` (75), `append_layout_body` `:3768`, `append_name_category` `:3778`, `format_prelude_implicit_group` `:3797`; `const LAYOUT_ROW_CAP` `:3564`, `const LAYOUT_BREAK_THRESHOLD` `:3568` | |

### 1.3 `repl/commands.rs` — the `handle_*` battery (prod ≈ 1,290)

Every slash-command handler and its command-private helpers **except** `handle_search`
(→ search.rs). `handle_imports`/`handle_exports` fold in here (the FIXME names them).

| Item | `:line` |
|---|---|
| `handle_sig` `:805`, `handle_doc` `:842`, `handle_list` `:892` (81), `handle_context` `:973`, `agent_context_driver_text` `:1002` | |
| `handle_refs` `:1027`, `collect_referers` `:1066`, `handle_tests_for` `:1106` | |
| `handle_mod` `:1552`, `handle_source` `:1591`, `handle_sexp_cmd` `:1613`, `handle_ast` `:1628`, `handle_clif` `:1640`, `handle_disasm` `:1662` | |
| `handle_info` `:1683` (62), `info_definition_source` `:1745`, `handle_type` `:1793`, `typecheck_only` `:1815`, `wrap_exprs_as_synthetic_defns` `:1856`, `lift_expr_type` `:1886`, `prelude_implicit_names` `:1908` | |
| `handle_imports` `:1947` (113), `classify_import` `:2060`, `resolve_to_definition` `:2080`, `handle_exports` `:2100` (80); `enum ImportClass` `:3555` | |
| `handle_expand` `:2180`, `compile_pending_macros` `:2199` (95), `expand_form_sexp` `:2294` | |
| `handle_time` `:2319`, `handle_mem` `:2347`, `handle_run_tests` `:2389`, `handle_platform_schema` `:2420`, `handle_run_all_tests` `:2438`, `format_test_run` `:2461`, `is_test_function` `:3574` | |

### 1.4 residual `repl.rs` — dispatch + prompt/banner/line-editor + the shared toolbox (prod ≈ 790)

The §3.3 Wave-D allocation `repl.rs` was always meant to be, plus the cross-cutting leaf
(§1.5).

| Item | `:line` |
|---|---|
| Parse/dispatch: `parse_slash_command` `:165`, `print_help` `:210`, `run_shell_command` `:249`, `process_commands` `:473`, `dispatch_command` `:512` (167); `enum ReplCommand<'a>` `:97`, `const QUIT_SENTINEL` `:161` | |
| Prompt/banner/editor: `print_banner` `:2544`, `current_module_name` `:2554`, `prompt_string` `:2576`, `continuation_prompt_string` `:2583`, `parens_balanced` `:2589`, `pretty_print` `:2594` | |
| Input classification: `special_form_feedback` `:2515`, `lookup_special_form` `:2530`, `is_repair_definition_turn` `:3860` | |
| **Shared toolbox (§1.5)** | see §1.5 |

### 1.5 The shared toolbox — the one real placement decision

Two clusters of helpers are called from **more than one** target file. They are the
`support.rs` analogue of the 0580 cut, and they stay in **residual `repl.rs`** as the bottom
layer (all four files may depend on `repl.rs`; siblings do not depend on each other except
`commands.rs` → `search.rs` for the referer scan, an acceptable one-way edge).

- **Resolution glue** (called from format.rs, commands.rs, search.rs, and `eval.rs`):
  `lookup_with_prelude_fallback` `:679`, `lookup_with_prelude_fallback_opt` `:700`,
  `resolve_symbol_arg` `:772`, `resolve_entry_arg` `:791`, `get_introspection` `:1581`.
  These are the canonical single-sourced lookup path (`src/CLAUDE.md` §"Prelude as a
  resolution FALLBACK"); duplicating them would be a Principle-7 mirror. `pub(crate)`.
- **Referer-scan toolbox** (called from `scan_referers` in search.rs AND `collect_referers`
  in commands.rs): `body_references` `:3588`, `sexp_references` `:3600`,
  `source_tokens_reference` `:3614`, `symbol_token_matches` `:3666`, `is_operator_name`
  `:3673`. `pub(crate)` in residual `repl.rs`; both callers reach them via `crate::repl::`.

**Do not duplicate either cluster into two siblings** — that is exactly the divergent-mirror
class the project fights (`/review` watches for it).

### 1.6 Budget check

| File | prod ≈ | + travelling tests (§2) | total ≈ |
|---|---:|---:|---:|
| `repl/search.rs` | 460 | ~250 | ~710 |
| `repl/format.rs` | 1,050 | ~430 (after §1.5 valve + fq_arg split) | ~1,480 |
| `repl/commands.rs` | 1,290 | ~200 | ~1,490 |
| residual `repl.rs` | 790 | ~60 | ~850 |

FORMAT and COMMANDS are the tight ones and land just under ~1,500 **only with the §2 test
apportionment applied**. **Pressure valve, pre-authorised:** if `repl/format.rs` measures
over ~1,500 after the move, relocate the **layout-render subfamily** (`format_symbol_layout`
+ `append_layout_body` + `append_name_category` + `format_prelude_implicit_group` + the two
`LAYOUT_*` consts + `prelude_group_layout_tests`) to `repl/commands.rs` — its only consumers
are `handle_list`/`handle_imports` (COMMANDS). This is a sanctioned second cut, not a design
change; `/dev` takes it if and only if the measured line count needs it.

## 2. The test split (`:3886–5234`, ~1,470 lines, 11 test mods)

Tests move with their subjects. The decisive problem is `fq_arg_tests` (`:4328–5010`, ~682
lines), which exercises FORMAT + COMMANDS + SEARCH in one module — it **must split** along
the same three-way seam (it cannot travel wholesale without bloating one file past budget).

| Test mod | `:lines` | goes to |
|---|---|---|
| `search_message_selection_tests` `:3920`, `search_excerpt_tests` `:5189` | | `repl/search.rs` |
| `collect_related_tests` `:3982`, `overloaded_display_tests` `:4138`, `trait_related_section_tests` `:5012`, `styling_colour_on_tests` `:3372` (the two search-row cells move to search.rs) | | `repl/format.rs` |
| `prelude_group_layout_tests` `:5088` | | `repl/format.rs` **or** commands.rs (moves with the §1.5 layout valve if taken) |
| `mem_command_tests` `:4081`, `sig_display_helper_tests` `:4244` | | `repl/commands.rs` (sig helper touches `format_def_entry` — assertions on the `handle_sig` surface) |
| `repair_definition_turn_tests` `:3887` | | residual `repl.rs` |
| **`fq_arg_tests` `:4328` — SPLIT** | | FORMAT cells (`format_type_display`/`format_trait_display`/`impls_for_type_in_view`/builtin-type display) → format.rs; COMMANDS cells (`handle_info`/`handle_doc`/`handle_sig`, `resolve_*_arg`) → commands.rs; SEARCH cell (`exact_in_scope_hit`) → search.rs |

## 3. Migration order + hazard list for `/dev`

One stage (no in-place phase-split precursor):

| Step | Action | Gate |
|---|---|---|
| 1 | Create `src/repl/mod.rs` from `repl.rs`'s residual (§1.4); `mod search; mod format; mod commands;` (all `pub(crate)`, private within the binary). Move §1.1–§1.3 items into the sibling files; split the tests per §2. | compiles |
| 2 | Adjust visibility: shared toolbox (§1.5) → `pub(crate)`; cross-file `impl CompilerSession` methods → `pub(crate)`; sibling-only free fns → `pub(super)`; **never `pub`**. | zero unused/private-in-public warnings |
| 3 | Update `int.md` §3.3 + `src/CLAUDE.md` §Session/REPL module map to the four-file map (same change-set). | — |

### Hazard list

1. **Visibility-widening is the only thing that can regress the surface** — and even a stray
   `pub` cannot leak (private `mod repl` in a binary), but keep minimum visibility as the
   structural guard (Principle 18). The compiler's dead-code/private-in-public warnings are
   the cheap signal a cut is clean.
2. **`fq_arg_tests` must split** (§2) — do not park it whole in one file "to move later"; a
   1,500-line breach is the FIXME's own failure condition.
3. **The §1.5 toolbox must not be duplicated** — one home (residual `repl.rs`), both callers
   reach it via `crate::repl::`.
4. **The layout valve (§1.6)** is applied on the measured line count, not speculatively.
5. **Golden REPL e2e must stay byte-identical** — the move touches no output-producing logic;
   any golden diff is a mis-move, not an expected change.

## 4. Behaviour-preserving acceptance contract

- **Golden REPL e2e green + unit tier green** — the conformance gate (a binary has no
  baseline; BC §6).
- **Zero movement on any library crate's `public-api.txt`** — none is touched (src/-only).
- **No file in the `repl/` family exceeds ~1,500 lines** (§1.6 budget, valve applied if
  measured over).
- **`int.md` §3.3 + `src/CLAUDE.md` module map updated in the same change-set** (couples with
  FIXME 0607).

## Cross-references

- `design/typecheck/program-decomposition.md` — the S109 `program.rs` cut this mirrors (the
  0580 template: sign-off first, mechanical move last, zero-diff).
- `src/CLAUDE.md` §"Session/REPL module map" — the as-built module allocation this cut
  completes.
- `design/int/index-worker-isolation.md` — `repl/search.rs` is the UI half of the indexer
  this doc governs.
