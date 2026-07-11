# S107 Test Plan — REPL & agent output rendering ergonomics (Phase 3)

Sprint 107 covers four findings from S106 close-out testing (`sprints/SPRINT.md`):

1. deftype nameless constructor-field rejection (correctness; `/dev(cranelisp-frontend)`).
2. FIXME 0554 — `/sexp` & `/source` aligned `let`/`match` column layout (`repl/spec.md` §3.11).
3. FIXME 0556 — agent `▌` gutter breaks copy-paste (§17.2 item 3 / §17.13.2 / §10.3).
4. FIXME 0555 — agent terminal answer not streamed (§17.22).

This plan is the **QA-first Stage-1 drafting order** for Phase 5. Every test below is
failing-not-ignored on HEAD (per `memory/feedback_failing_not_ignored.md`); the owning
`/dev` seam flips it green. Agent items (3, 4) are `--features agent`-gated and drive the
real binary through the `CRANELISP_AGENT_PROVIDER=stub` mechanism (`tests/agent.rs`,
`src/agent/stub.rs`). All new tests carry a `// spec:` back-trace and a row here.

Two tiers, no middle (`tests/CLAUDE.md`): `/qa` owns the e2e; the paired **unit** tier
(fence-buffering, differential-invariant-vs-`render_agent_prose`, §14.6 leaf-styling,
frontend AST-build rejection) is `/dev`-owned in the owning crate, written in the same
change-set as each fix. This plan **names** the unit obligations so Phase 5 does not
miss them, but `/qa` does not author them.

---

## Item 1 — deftype nameless constructor-field rejection

**Spec:** `spec/05-definitions.md` §5.2 (grammar: `field_def = colon_prefix symbol`;
`field_list = '[' field_def* ']'`; a data constructor is `'(' name docstring? field_list ')'`).
A bare `(L :Int)` — no brackets, no field name — is not a valid constructor.
**Root cause (arch-pinned):** `crates/cranelisp-frontend/src/ast_builder.rs::build_constructor_def`
(~L604–612) `else { vec![] }` silently drops the trailing non-bracket form → `L`/`R`
collapse to nullary constructors (a silent enum). Fix = reject a trailing non-bracket,
non-docstring form.

| Test | File | Tier | Assertion target | Polarity |
|---|---|---|---|---|
| `deftype_ctor_nameless_type_field_rejected_neg` (EXISTS, RED) | `tests/spec_05_definitions.rs` | e2e | `(deftype Rotation (L :Int) (R :Int))` ⇒ stdout contains `error` (field not silently dropped) | negative — flips GREEN on the frontend fix |
| `deftype_sum_bracketed_field_still_constructs` (ADD) | `tests/spec_05_definitions.rs` | e2e | companion **positive** guard: a correctly-bracketed sum type `(deftype Rotation (L [:Int n]) (R [:Int n]))` still constructs — `L` introspects as `(Fn [primitives/Int] user/Rotation)` and `(L 5)` builds a value. Must stay GREEN across the fix (proves the reject is narrow, not a blanket ctor break) | positive |
| `deftype_ctor_nameless_field_not_nullary_neg` (ADD) | `tests/spec_05_definitions.rs` | e2e | tighter negative: after the rejected `(L :Int)` form, `L` MUST NOT introspect as a nullary value `:user/Rotation Rotation.L` (the exact silent-enum symptom) — the field is not silently swallowed into a nullary ctor | negative |

**`/dev(cranelisp-frontend)` unit obligation (not `/qa`):** a `#[cfg(test)]` test in
`ast_builder.rs` asserting `build_constructor_def` on the `(L :Int)` sexp returns `Err`
(the trailing non-bracket, non-docstring rejection) — the exact seam, per the
unit-test-per-fix discipline.

---

## Item 2 — FIXME 0554: `/sexp` & `/source` aligned `let`/`match` column layout

**Spec:** `repl/spec.md` §3.11 (P0–P5 + the byte-exact `rotate` worked example). Layout is
a **byte-reproducible MUST** (colour-off); the §3.11 worked output is the assertion target.
**Home file:** `tests/display_exact.rs` (byte-exact block assertions; reuse its
`assert_golden_masked` / block-exact helper — no timing mask needed here). `/source`
shares `crate::pretty::pretty_print`, so both commands assert the same bytes.

| Test | Tier | Assertion target | Polarity |
|---|---|---|---|
| `sexp_rotate_aligned_let_match_byte_exact` | e2e | Define the §3.11 `rotate` fixture, then `/sexp rotate`; assert the **byte-exact** 9-line block from §3.11 appears verbatim (the aligned `let` left col at 8 / right col at 18; the nested two-arm `match` arm col at 28 / right col at 34; the multi-line `if` body at col 20). Byte-exact substring `assert` of the pinned block. | positive (byte-exact) |
| `source_rotate_aligned_matches_sexp_byte_exact` | e2e | `/source rotate` on the same fixture emits the **same** byte-exact block (shared `pretty_print` path — the two must not diverge). | positive (parity) |
| `sexp_two_arm_match_forces_multiline_neg` | e2e | P0 trigger: a 2-arm `match` that would fit a flat line MUST render multi-line aligned — assert the arms are on separate lines and NOT collapsed onto one (the pre-S107 smear must not recur: a left term, the next left term, and a right term MUST NOT share a line). | negative |
| `sexp_single_pair_let_flat_fallback` | e2e | P5/P0 edge: a `let` with **one** binding pair (nothing to align) follows the pre-existing flat/threshold layout unchanged — NOT forced into two-column layout. | positive (edge) |
| `sexp_odd_count_match_arm_no_crash_neg` | e2e | P5 graceful fallback: a recognised vector with an **odd** element count (malformed `match [(L l) (- 0 l) (R r)]`) MUST fall back to the non-pair bracket layout, MUST NOT crash and MUST NOT drop elements (all three tokens still present in output; exit non-panic). | negative |
| `sexp_empty_let_binding_no_crash` | e2e | 0-pair edge: `(let [] body)` — empty binding vector — renders without crash and with no spurious alignment padding. | positive (edge) |

Determinism note for Phase 5: the byte-exact assertions run under the non-TTY REPL, which
writes the `user> ` prompt verbatim (`src/repl_input.rs`); assert the pretty-printed **block**
as a byte-exact substring, not whole-stdout equality (the prompt/echo lines surround it).
`PreludeVariant::PrimitivesOnly` (the fixture needs `-`/`+`/`<` as bare symbols or defines
them inline — keep the fixture free-standing per `tests/CLAUDE.md`; if operators are needed
use `TestPrelude`).

**`/dev(src)` unit obligation (not `/qa`):** `src/pretty.rs` `#[cfg(test)]` tests over the
P0–P5 rules **on the `Sexp` tree** (Phase-2 durability constraint: structural pair-awareness,
not string post-processing) — per-rule: W computation per vector, right-column position,
P4 multi-line right-term indent, P5 odd-count fallback.

---

## Item 3 — FIXME 0556: agent gutter copy shape (`--features agent`)

**Spec:** `repl/spec.md` §17.2 item 3, §17.13.2 "Copy-clean, un-guttered [S107]", §10.3
(the "Agent prose frame" role row). Normative MUST: agent-emitted ```lisp / ```cranelisp
code fences render with **NO per-line `▌` gutter on any code line**, and the code block's
bytes are **byte-identical (colour-off) to `pretty_print_str` / `/sexp` output for the same
form** — nothing prepended to any line. Surrounding **prose** lines keep their `▌` gutter.
**Home file:** `tests/agent.rs` (`#[cfg(feature = "agent")]`, stub-provider e2e).

Current behaviour (`src/style.rs::agent_prose`) gutters **every** line via `text.lines()`,
so today the ```lisp fence lines carry `▌ ` — the exact copy-pollution 0556 fixes. The fix is
a render-side structural split in `src/agent/render.rs` (gutter prose runs; frame code fences
un-guttered) — sequenced **before** 0555 (it defines the code/prose framing split the
streaming renderer consumes).

| Test | Tier | Assertion target | Polarity |
|---|---|---|---|
| `agent_lisp_fence_code_lines_ungutter_neg` | e2e | `/ask` turn, scripted `done:` prose + a ```lisp fence (`--no-color`). Assert **every code line** of the pretty-printed form carries **NO `▌`** prefix — split stdout into lines; the lines belonging to the rendered form must be gutter-free. This is the core 0556 MUST. RED on HEAD (all lines guttered). | negative (absence of gutter on code) |
| `agent_lisp_fence_bytes_equal_sexp_output` | e2e | The rendered code block bytes are **byte-identical (colour-off)** to `/sexp`/`pretty_print_str` for the same form: in one session, get `/sexp double` output AND the agent-shown ```lisp double fence; assert the pretty-printed form block is byte-identical between the two (nothing prepended). | positive (byte parity) |
| `agent_prose_lines_keep_gutter` | e2e | The surrounding **prose** lines (before/after the fence) MUST still carry the `▌` gutter (the split is code-only; prose framing is preserved). | positive (gutter retained on prose) |

### Re-baseline set (existing tests that MUST be updated when 0556 lands)

Named explicitly so Phase 5 does not miss them (§17.2 "Guards this touches"):

| Existing test | File | Tier | Owner | Action |
|---|---|---|---|---|
| `agent_output_no_literal_ansi_escape_when_color_off_neg` | `tests/agent.rs` | e2e | `/qa` | Currently RED (raw fence survives). Post-fix the fence is pretty-printed **and un-guttered** — **tighten**: add the "code lines carry no `▌`" assertion; keep "no raw ```", "no `\x1b[`", "prose `▌` present". |
| `agent_output_lisp_fence_pretty_printed_styled` | `tests/agent.rs` | e2e | `/qa` | Add the un-guttered-code assertion alongside the existing pretty-print / well-formed-SGR checks. |
| `agent_session_render_golden_transcript` | `tests/agent.rs` | e2e | `/qa` | The §17.13.3 **non-TTY whole-session golden** the spec names for re-baseline. Tighten to the un-guttered code shape: code lines gutter-free, prose lines guttered, pull line carries `agent>`, no raw fence, `--no-color` clean. |
| `agent_prose_markdown_formatted_for_terminal`, `agent_prose_markdown_no_color_clean_neg` | `tests/agent.rs` | e2e | `/qa` | Prose-only (no fence) — **NOT affected** (prose keeps its gutter). Listed to confirm they are deliberately out of the re-baseline. |
| `lisp_fence_color_on_emits_well_formed_sgr`, `render_agent_prose_frames_and_formats`, `split_fences_*` | `src/agent/render.rs` | unit | `/dev(src)` | The **§14.6 leaf-styling guard**. `/dev` re-baselines these to the un-guttered code shape in the same change-set (render-side split). `/qa` does not edit them — flagged as a `/dev` obligation. |

---

## Item 4 — FIXME 0555: streaming the agent's terminal answer (`--features agent`)

**Spec:** `repl/spec.md` §17.22. Terminal `Done` prose streams line-by-line as deltas
arrive; a ```lisp fence is **buffered** while open and emitted **formatted, un-guttered** at
fence-close; tool-call turns are NOT streamed (explicit seam). The load-bearing MUST is the
**differential invariant**: streamed-then-concatenated output is **byte-identical** to
`render_agent_prose` over the same complete answer text (colour-off) — streaming changes only
*when* bytes reach the screen, never *which* bytes. **Home file:** `tests/agent.rs`.
Arch decomposition S1–S5 (`AgentModel::complete_streaming` membrane → provider impl →
`StreamingRenderer` → `agent_turn` wiring → coverage). 0556 lands first (framing split).

| Test | Tier | Assertion target | Polarity |
|---|---|---|---|
| `agent_terminal_answer_streams_incrementally` | e2e | A multi-delta stub answer (several deltas, no fence) ⇒ the terminal prose renders **incrementally**, framed. Observable target: the framed prose lines all appear, in order, inside the `▌` frame. (True incrementality — bytes-before-completion — is not directly observable through a captured pipe; see harness gap G-1. This test pins the *rendered result* of the streaming path over a multi-delta script.) | positive |
| `agent_streaming_bytes_equal_single_shot` (differential-invariant e2e proxy) | e2e | Feed the **same** answer text (prose + a ```lisp fence) two ways: (a) one whole delta (the fallback/one-delta case) and (b) many deltas; assert the two agent-turn stdout regions are **byte-identical** (colour-off). This proxies the §17.22 invariant end-to-end: delta chunking changes only *when*, not *which*, bytes — same gutter on prose, same un-guttered formatted fence. | positive (byte parity across chunking) |
| `agent_streaming_fence_emitted_whole_at_close_neg` | e2e | With the ```lisp fence split **across delta boundaries**, the raw fence markers (` ``` `) MUST NOT survive and no half-formatted partial fence appears mid-stream — the formatted block appears whole at fence-close (buffer-within-fence). | negative (no raw / partial fence) |
| `agent_tool_call_turn_not_streamed` | e2e | A tool-call turn (`tool: source …`) renders as today (unframed pull + result, after the tool runs) — the streaming path applies only to the terminal `Done` prose (explicit S107 seam). | positive (seam boundary) |
| `agent_non_streaming_provider_degrades` | e2e | Fallback: a one-delta answer (the non-streaming degrade) renders exactly as the all-at-once render — proven by `agent_streaming_bytes_equal_single_shot`'s (a) leg; this row pins the standalone one-delta case still frames + formats correctly. | positive (fallback) |

**`/dev(src)` unit obligations (not `/qa`) — the load-bearing tier for 0555:**

- **Differential invariant (pure).** `src/agent/render.rs` `#[cfg(test)]`: drive the
  `StreamingRenderer` over a multi-delta split of an answer, concatenate its emission, and
  assert **byte-equality** with `render_agent_prose(whole_text)` (colour-off). This is the
  direct `== render_agent_prose` MUST — the e2e can only observe the proxy (byte parity across
  chunking); the pure invariant lives here.
- **Fence-buffering.** `StreamingRenderer` unit tests: a partial fence held (not echoed raw)
  while open; flushed **formatted** through `pretty_print_str` on the closing fence; a prose
  line flushed the moment its newline arrives; a partial trailing line withheld until newline.
- **Membrane default-fallback (S1).** `AgentModel::complete_streaming` default impl forwards
  the whole prose as one delta (bounds blast radius; non-streaming providers keep working).

---

## Harness gaps — name them now so Phase 5 has no surprises

**G-1 — the stub cannot script multiple deltas (BLOCKS item 4 e2e).** `src/agent/stub.rs::parse_script`
collapses `done:` + continuation `prose:` lines into **one** `ModelResponse::Done`, and
`AgentModel` has only `complete()` — there is **no `complete_streaming` and no delta channel**
on HEAD (S1 is Phase-5 `/dev` work). The streaming e2e (`agent_terminal_answer_streams_incrementally`,
`agent_streaming_*`) need the stub to emit a scripted answer as **multiple deltas within one
terminal turn**. Phase-5 prerequisite (`/dev(src)`, same change-set as S1/S2/S5): (a) add
`AgentModel::complete_streaming(&mut self, req, sink: &mut dyn FnMut(&str))`; (b) give the
stub a delta channel — a DSL directive (e.g. `delta:` lines, each one delta) **or** have
`StubModel::complete_streaming` split its `Done` prose at a scripted boundary — so the test
controls delta boundaries (including a boundary **inside** a ```lisp fence for the
fence-buffering guard). `/qa` cannot author the streaming e2e until this stub seam exists;
the tests are drafted against the seam and go RED (compile-fail is a valid loud signal per
`tests/CLAUDE.md`) or are staged behind the S1 landing. Flagged to `/dev(src)`.

**G-2 — true incrementality is not observable through the captured pipe.** The e2e harness
pipes stdout and reads it **after** the process exits (`CrOutput.stdout` is the whole capture),
so a test cannot observe "bytes arrived before completion." The e2e therefore pins the
**rendered result** of the streaming path (order, framing, byte-parity across chunking), and
the *timing* of incrementality is a `/dev` unit concern (the `StreamingRenderer` emits per
delta). This is why the differential-invariant **pure** `== render_agent_prose` test is
unit-tier — the e2e observes only the byte-parity proxy (G-1's two-way feed). Not a blocker;
a scope boundary to record.

**G-3 — byte-exact capture is fine, but the prompt interleaves.** `CrOutput.stdout` is the raw
byte-exact subprocess capture (no normalization) — byte-exact `/sexp`/agent assertions are
supported. But the non-TTY REPL writes `user> ` prompts verbatim (`src/repl_input.rs`); a
byte-exact assertion must target the pretty-printed **block** as a byte-exact **substring**,
not whole-stdout equality. Reuse `tests/display_exact.rs`'s block-exact helper. No new harness
work; a drafting rule for item 2 and item 3's byte-parity.

**G-4 — no `--color=force` path (pre-existing).** The e2e pipe forces colour **off**
(`style::detect_color`: non-TTY ⇒ off; no `--color=force`, `repl/spec.md` §10.7). So the
**colour-ON** half of the differential invariant and the well-formed-SGR guards are only
reachable in `/dev` unit tests (via the `style::test_support::ColorGuard` force seam already
used by `lisp_fence_color_on_emits_well_formed_sgr`). All `/qa` e2e byte-exact / byte-parity
assertions run colour-off. Pre-existing; carried forward, not new to S107.

---

## Phase-5 Stage-1 drafting order (for `/sprint` + `/qa` in Phase 5)

1. **Item 1** — add the two deftype companions (`display`/positive + tighter negative) beside
   the existing RED; independent of the render work, can land first (frontend fix is parallel).
2. **Item 2** — draft the `display_exact.rs` byte-exact `/sexp`/`/source` `rotate` block +
   P0/P5 edge guards; RED until `src/pretty.rs` pair-awareness lands.
3. **Item 3** — draft the three new gutter e2e + **schedule the four re-baseline edits** to
   the existing agent goldens (tighten to un-guttered code shape); RED until the §14 render
   split lands. 0556 before 0555.
4. **Item 4** — draft the streaming e2e **against the G-1 stub seam** (`complete_streaming` +
   delta channel); the pure differential-invariant + fence-buffering tests are `/dev` unit
   obligations named here. RED / staged until S1–S5 land.

**Ledger:** add each new RED to `tests/plan/ledger.md` at authoring with SHA + signature +
owner (`/dev(cranelisp-frontend)` for item 1; `/dev(src)` for items 2–4), per the
required-fields list.
