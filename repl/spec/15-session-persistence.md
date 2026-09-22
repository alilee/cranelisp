> [REPL specification index](index.md)

## 15. REPL Session Persistence [R4 S52]

### 15.1 Source Regeneration [Tested tests/repl_persist::persist_user_cl_is_created_with_definition_after_session]

The REPL MUST persist interactive definitions to disk by maintaining a backing `.cl` file for the entry module (e.g. `user.cl`). When the user enters a definition that compiles successfully:

1. The definition MUST be compiled and installed in the session. [R4 S52]
2. The entry module's backing `.cl` file MUST be **regenerated** atomically from the module's current state. The regeneration is performed by the REPL after eval — it is not part of the compilation or `.o` caching pipeline. [R4 S52]

The regenerated source file MUST be valid, parseable Cranelisp source — loading it through the normal module graph pipeline MUST reproduce the same session state. [R4 S52]

A definition entered in the session that fails to compile MUST NOT trigger regeneration and is never written. The backing file reflects the last successfully compiled state, plus any startup-failed source retained under §15.2.3. [Tested+Neg tests/repl_persist::persist_startup_failed_source_retained_until_same_name_repair_neg, tests/repl_persist::persist_failed_import_not_written_to_backing_neg, tests/repl_persist::persist_expression_only_session_leaves_hand_authored_user_cl_untouched — the failed-definition variant itself is not exercised; nearest cells are the failed structural form and the expression-only control]

### 15.2 Session Restore [Tested tests/repl_persist::persist_defn_survives_restart_via_user_cl]

On REPL startup, the entry module's backing `.cl` file MUST be loaded through the normal module graph pipeline (with cache hit for fast restore). Definitions from the previous session MUST survive restart — the user resumes where they left off. [R4 S52]

If the backing file does not exist (first session, or user deleted it), the REPL MUST start with an empty module. [R4 S52]

#### 15.2.1 Persistence Authority — Restoration Governs, Redefinition Wins [S113]

The backing `.cl` file is **authoritative for restoration only** — it establishes the definitions the session *starts with*, never overriding what the user enters next. The authority model is precise: [S113]

1. **Restoration.** On startup the backing file's definitions are loaded and become the session's initial state (§15.2). A directory holding a persisted `user.cl` (+ `.cranelisp-cache`) therefore **resumes the prior session**, not a fresh program. [S113]
2. **Redefinition wins.** Any definition entered in the session **replaces** a restored definition of the same name (§15.6) — just-entered source always governs. On-disk authority never overrides live input. [S113]
3. **Input is session input, not a fresh program.** Both interactive typing and **piped stdin** (`cranelisp < script.cl` run in a directory with a persisted `user.cl`) are evaluated **against the restored definitions**. A script that references a name it does not itself (re)define resolves that name to the **previous session's** binding — the input augments a resumed session, it does not start a clean one. This is the correct behaviour, but it is a **sharp edge** for anyone applying the `--run` mental model (a self-contained program) to a piped REPL session: the same script piped into an empty directory versus a directory carrying prior state can produce different results. Fresh-program semantics are `cranelisp --run script.cl` (§0.2) or a REPL launched in an **empty** working directory. [S113]

(Ruling record: PS-C1 in the S113 test plan at revision `7b1220c7` — the discriminator run settled that redefinition wins; the compiler behaves as designed. A companion note lives in the user guide's getting-started material.) [S113]

#### 15.2.2 Startup Restore Notice [S113]

Because a resumed session is not visually distinct from a fresh one, the self-documenting-REPL principle requires the session to **say** it resumed prior state. When startup restores a **non-empty** backing file, the REPL SHOULD emit a single R6-metadata line before the first prompt, naming how much state was restored and from where: [S113]

```
; resumed 7 definitions from user.cl
user>
```

- The count is the number of restored **definitions** (the §15.7 persisted forms), not transient expressions. The count MUST be **singular-aware** — `1 definition`, `N definitions`. [S113]
- The notice MUST be **suppressed when the backing file is absent or empty** — a first session in an empty directory MUST reach the prompt with no extra output, preserving the first-session experience (§6.2) and keeping fresh-directory session transcripts byte-identical. [S113]
- The notice is startup-only chrome (§10.3 metadata role), never persisted and never part of a value/definition response. [S113]

**Notice, not banner — the aesthetic call is settled (`/repl`, S114).** The restore
notice is rendered as an **R6 dim-metadata line** (§13 style register R6), grouped
with the other startup notices (the search-index notice, the `Cranelisp.toml`
create notice, §15.2.2's siblings), and is **not** part of the startup banner (§6.2).
The banner keeps its own identity styling and its ≤3-line budget — language name,
version, `/help` hint — describing *what the REPL is*; the restore notice is dim
chrome describing *what this particular startup did* (it resumed prior state).
Keeping the two visually distinct means the banner stays byte-stable across fresh
and resumed sessions, and the resume signal reads as the transient metadata it is,
in the same visual class as every other `[updated: …]` / index / config notice —
never as a headline. [S114]

**Interactive chrome — TTY-gated (`/repl` ruling, S114, FIXME 0700).** The restore notice is **interactive chrome for a human at the prompt**, in the same category as terminal styling (§10.1 TTY detection and suppression), the line editor and history (§10.8), and the search-index notice. Its whole purpose — telling a human that a resumed session is *not* the fresh one they might assume — has no addressee in a non-interactive session, whose consumer is a program or a golden-transcript harness that either already knows the working directory's state or requires byte-identity. The notice is therefore emitted **only when stdout/stdin is a TTY**; a **non-TTY session (piped stdin, harness, batch) MUST NOT emit it**, keeping restore-mode and fresh-mode non-interactive transcripts byte-identical (the §10.5 batch / mode-parity output-equivalence contract). This is the correct and settled behaviour, not a limitation: emitting the notice in non-TTY mode would diverge restore-mode transcripts from fresh-mode ones and disturb the output-equivalence harness for no reader benefit. [S114]

**Verification is split by tier.** Because the positive face is unauthorable in the non-TTY e2e harness, coverage divides: (a) the **decision** — `startup_restore_notice` returning the Some/None line with the correct singular-aware count and empty/absent suppression — is a **unit-tier** obligation (already unit-pinned in `src/session_v4/lifecycle.rs`); (b) the **non-emission in non-TTY mode** is the e2e-observable face, asserted by the mode-parity/output-equivalence goldens (a piped restart is byte-identical to a fresh one). The positive interactive face is confirmed by TTY session transcript, not a non-TTY golden. [S114]

**Implementation handoff (`/dev`, src/):** this notice is REPL boot-time runtime output — it requires `src/` code (the startup restore path), not a `repl/` config change. `/repl` specifies the wording, count semantics, empty-suppression rule, and the TTY gate above; `/dev` implements it at the session-restore seam behind the same `is_terminal()` gate the search-index notice uses. **Count source (`/dev`, Minor — FIXME 0707):** the count MUST be taken from the session's own restore record (the definitions that actually restored), **not** by re-reading and re-parsing the backing file — after a startup load failure (§15.2.3) a re-parse over-counts by including definitions that failed to restore, contradicting "restored definitions." [S113/S114]

#### 15.2.3 Startup Load Failure [Tested+Neg tests/repl_persist::persist_startup_load_failure_reaches_prompt_blocks_then_repairs, tests/repl_persist::persist_startup_failed_source_retained_until_same_name_repair_neg, tests/repl_persist::persist_startup_failed_source_survives_reset_then_other_definition — one module, non-TTY; report/refusal wording not spec-pinned]

If the persisted source (the backing `.cl` file, §15.1) fails to compile at startup, the REPL MUST report the load error and still reach a prompt.

The affected module MUST then enter an error-blocked state:

- ordinary expressions are refused;
- definition updates are accepted, so the user can repair the module at the prompt; and
- a successful repair clears the error-blocked state.

Each persisted definition that failed to compile at startup MUST keep its source text, verbatim, in every later regeneration of the backing file (§15.1) until a successful definition replaces it. A successful turn that defines a different name therefore MUST NOT remove the failed definition's source from the backing file. [Tested+Neg tests/repl_persist::persist_startup_failed_source_retained_until_same_name_repair_neg, tests/repl_persist::persist_startup_failed_source_survives_reset_then_other_definition]

Error blocking caused by a watched file changing during a session is specified separately (§14.4–§14.6).

### 15.3 Unified Development Model [R4 S52]

This design unifies interactive and file-based development:
- Interactive definitions are source files that happen to be managed by the REPL.
- File watching (§14) applies uniformly — external edits to the backing file MUST be picked up by the watcher and recompiled.
- The object cache (§14.7) accelerates both imported modules and the user's own work.

### 15.4 Regeneration Integrity [Tested tests/repl_persist::persist_user_cl_is_valid_source_with_topological_ordering]

The regenerated source file MUST satisfy the following invariants:

1. **Round-trip correctness:** Loading the regenerated file through the compiler MUST produce the same types, values, and module exports as the interactive session. [R4 S52]
2. **Authorship ordering:** Definitions MUST appear in the order they were registered with the session — file-loaded modules in source declaration order; REPL-introduced symbols appended in the order they were entered. Redefinition MUST NOT reorder; a redefined symbol keeps its original position. Cranelisp's cluster-atomic typecheck handles forward references natively, so dependency ordering is not a correctness requirement — the regenerated file reflects authorship intent. [R4 S52]
3. **Symbol qualification preservation:** The regenerated source MUST preserve the user's original qualification style. If the user wrote a fully-qualified reference (`core.option/Some`), it MUST remain fully-qualified. If the user wrote a bare name (`Some`) that was resolved via an import, it MUST remain bare. The regenerator MUST NOT rewrite bare names to qualified or vice versa. [R4 S52]
4. **Structural sections at top in fixed order:** Structural sections MUST appear at the top of the regenerated file in this fixed order: (a) platforms — `(declare-platform ...)` forms; (b) submodules — `(mod ...)` declarations; (c) exports — `(export ...)` forms; (d) imports — `(import ...)` forms. Within each section, items appear in authorship order (file parse order + REPL append). Definitions follow the four structural sections. [R4 S52]
5. **Comments:** The behaviour of comments in regenerated source is unspecified. The implementation MAY strip comments, preserve them, or handle them in any other way. [R4 S52]
6. **Source in cache metadata:** The `.meta.json` cache file MUST include all source text needed for regeneration, so that the REPL can restore the backing file from cache alone. [R4 S52]
7. **Authorship-intent rationale:** The regeneration invariants above (authorship ordering, fixed structural-section order, redef in place) collectively express a single intent — *principle of least surprise*. The regenerated file is a faithful record of what the user typed and when, not a derived form computed from compilation properties. The compiler's pipeline already handles forward references and dependency resolution; regeneration's job is authorship fidelity, not re-deriving correctness. [R4 S52]

**Template qualification to round-trip correctness. [S121]** Rule 1 reproduces
the current authored source, types, exports, and ordinary values. It does not
preserve historical generated code that is absent from that source:

- persisted authored macro calls are re-expanded using the macro definition
  current at reload or restart; and
- an authored `impl` that omits a default method re-materializes that method
  using the trait default body current at reload or restart.

Accordingly, an already-compiled expansion or generated default realization
may retain its earlier body in the live session after a future-only template
redefinition, then acquire the latest body when source is recompiled. This is
the only qualification introduced here; it does not permit rewriting authored
source or changing an existing live realization without its specified
typecheck/re-`impl` boundary (§18.4, §18.6).

### 15.5 File Watching Integration [R4 S52]

The file watcher (§14) MUST ignore writes triggered by the REPL's own source regeneration. Self-triggered writes MUST NOT cause a recompilation cycle. External edits to the backing file (e.g. from a text editor) MUST be detected and recompiled normally. [R4 S52]

### 15.6 Redefinition [Tested tests/repl_lifecycle::redefinition_replaces_value]

When the user successfully redefines a name that already exists in the session,
the regenerated source file MUST contain only the latest definition — the
previous definition MUST be replaced, not duplicated. A rejected redefinition
MUST NOT change the regenerated source. [R4 S52] [S121]

The declaration-class rules, atomic rejection behavior, and template
reconstruction qualifications are specified in §18. [S121]

A live redefinition cannot change an existing callable or macro declaration's
visibility. Such a rejected attempt does not change this file. The visibility
may instead change when externally changed persisted source is loaded at reload
or restart; introducing a new canonical name is the live-session alternative.

### 15.7 Backing-File Content — Definitions and Structural Forms Only [S106]

The regenerated backing `.cl` file MUST contain **definitions and structural forms only**.
Transient, **non-defining top-level expression evaluations are session-only and MUST NOT be
persisted** to the backing source file. (`/arch` ruling, S106, FIXME 0549 — reconciled against the
persisted-`__expr` reload model of FIXMEs 0532/0537; the exclusion is sound because nothing in the
T1-reload / monomorphisation / cache-restore paths requires the expression to be in the *backing
file* — the in-session symbol-table entry is unaffected, only its source emission is suppressed.)
[S106]

The boundary is precise:

- **Persisted (module content):** definitions — `defn`, `deftype`, `deftrait`, `impl`, `defmacro`
  — and structural forms — `mod`, `import`, `export`, `declare-platform` (the §15.4 rule-4
  structural sections). These are the module the user is building. [S106]
- **NOT persisted (transient session output):** bare top-level **expression** evaluations
  (e.g. `(+ 1 2)`, `(print "hello")`). A REPL top-level expression is recorded internally as a
  synthetic `__expr`-named entry so it can be evaluated and displayed; that entry is **session
  state, not module content**, and MUST be excluded from source regeneration. Persisting it would
  re-materialise the expression as module content on the next load — re-running it or leaving dead
  code — polluting the module the user is building. [S106]

**Why this is clean, not a loss of behaviour:** top-level expressions are a **REPL-interactive-only
construct** (`spec/02-grammar.md` §2.1; a top-level expression in module-body position is "ambiguous
and fragile", `spec/08-modules.md` §8.16.6). There is no module-init-evaluates-top-level-expressions
semantics to preserve — batch mode runs `main` — so excluding `__expr` forms from the backing file
is semantically clean. This settled scribe **reverses** the earlier deliberate persist-`__expr`
posture per the user ruling. [S106]
